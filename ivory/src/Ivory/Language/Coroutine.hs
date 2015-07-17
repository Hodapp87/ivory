{- |
Module: Coroutine.hs
Description: Resumable coroutines implementation
Copyright: (c) 2014 Galois, Inc.

This is an implementation of coroutines in Ivory.  These coroutines:

  * may be suspended and resumed,
  * are parametrized over any memory-area type ('Area'), /(CMH: Is this right?
Must it also have IvoryVar?)/
  * cannot return values, but can receive values when they are resumed,
  * can have only one instance executing at once, given a particular coroutine
name and Ivory module.

CMH, current work-in-progress:

  * I have decided that the best way to compose two coroutines is that the
caller needs to set its own continuation function in the continuation of the
callee.  This would be a sort of specialized 'yield' function which sets that
value in the specified coroutine's continuation, goes through the motions of
suspending (but without returning), and calls that same coroutine's
continuation function.
  * Upon that coroutine exiting (not just returning), it calls the return
continuation function set in its own continuation.  Is this correct, or does
it need a more explicit way of yielding 'back'?  If one yields back, this would
have to take an argument of the same type as the coroutine, and it would call
to the return continuation function.  This would require runtime checks: that
function pointer could be null depending on how the coroutine was called.
  * I have this *field* added to the continuation struct, and I think the type
is correct.
  * I do not have it being set or used.

-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Ivory.Language.Coroutine (
  -- * Usage Notes
  -- $usageNotes
  
  -- * Implementation Notes
  -- $implNotes
  
  Coroutine(..), CoroutineBody(..), coroutine,
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Fix
import qualified Data.DList as D
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.Monoid
import Ivory.Language.Area
import Ivory.Language.Array
import Ivory.Language.Effects
import Ivory.Language.IBool
import Ivory.Language.Module
import Ivory.Language.Monad
import Ivory.Language.Proc
import Ivory.Language.Proxy
import Ivory.Language.Ref
import qualified Ivory.Language.Syntax as AST
import Ivory.Language.Type
import qualified MonadLib

-- Optimizations TODO:
-- TODO: if every block yields, don't generate a loop
-- TODO: re-use continuation variables that have gone out of scope
-- TODO: full liveness analysis to maximize re-use
-- TODO: only extract a variable to the continuation if it is live across a suspend

{- $usageNotes

The coroutine itself is presented as a function which has one argument,
@yield@.  @yield@ suspends the coroutine's execution at the point of usage.

'coroutineRun' (given an argument of 'false') then resumes the suspended
coroutine at that point, passing in a value in the process.

-}

{- $implNotes

Coroutines are implemented as a single large C function, mainly as a series of
branches inside of a single infinite loop.

It was mentioned that @yield@ /suspends/ a coroutine for later resumption.
The state of the computation to be resumed later - that is, its
/continuation/ - is stored in a C struct, not visible to the outer Ivory code,
but denoted internally with a suffix of @_continuation@.  This C struct
contains a state variable and every local variable that is created.

At each @yield@, after collecting the current computation state into the
continuation, the C function breaks out of its loop and returns.

The @yield@ action is implemented as a sort of pseudo-function call which is
given a purposely-invalid name (see 'yieldName'). This Ivory call does not
become an actual function call in generated code, but rather, the code is
suspended right there.  (See the 'extractLocals' and 'addYield' functions.)

The pseudo-function call returns a 'ConstRef' to the coroutine's type.  Of
course, no actual function call exists, but the action itself still returns
something - hence, Ivory code is able to refer to the return value of a
@yield@.  Dereferences to it via 'deref' are turned to references to the
continuation struct.

As this @yield@ action is an Ivory effect, it can be passed at the Haskell
level, but it cannot be passed as a C value. (If one could hypothetically run
'procPtr' on it, then one could pass it around as a value, but any attempt to
call it outside of the same coroutine would result in either an invalid
function call, or a suspend & return of a different coroutine.)

-}

-- | Concrete representation of a coroutine; use 'coroutine' to produce one.
data Coroutine a = Coroutine
  { -- | Name of the coroutine (must be a valid C identifier)
    coroutineName :: String
    -- | Ivory effect for initializing a coroutine (if first argument is
    -- 'true'), or resuming it (if first argument is 'false').  The second
    -- argument is passed to the coroutine when resuming, and ignored when
    -- initializing.
  , coroutineRun :: forall eff s s'. GetAlloc eff ~ Scope s' =>
                    IBool -> ConstRef s a -> Ivory eff ()
    -- | The components a 'Module' will need for this coroutine
  , coroutineDef :: ModuleDef
  }

-- | The definition of a coroutine body, in the form of a function taking one
-- argument: an Ivory effect that is the @yield@ action which suspends the
-- coroutine, and sets the point at which 'coroutineRun' resumes it, passing a
-- value.
newtype CoroutineBody a =
  CoroutineBody (forall s1 s2 .
                 (forall b .
                  Ivory ('Effects (Returns ()) b (Scope s2)) (Ref s1 a)) ->
                         Ivory (ProcEffects s2 ()) ())

-- | Smart constructor for a 'Coroutine'
coroutine :: forall a. IvoryArea a =>
             String -- ^ Coroutine name (must be a valid C identifier)
             -> CoroutineBody a -- ^ Coroutine definition
             -> Coroutine a
coroutine name (CoroutineBody fromYield) = Coroutine { .. }
  where
  ((), CodeBlock { blockStmts = rawCode }) =
    runIvory $ fromYield $ call (proc yieldName $ body $ return ())
  -- The above 'call (proc yieldName ...)' is a pseudo-call, returning type
  -- 'a', that is later extracted in the AST and replaced.
{- CMH: How would I make another pseudo-call to handle the yield-to function?
Is yieldTo the right name?  What about yieldBack, or whatever?
-}

  params = CoroutineParams
           { getCont = AST.ExpLabel strTy $ AST.ExpAddrOfGlobal $
                       AST.areaSym contArea
           , getBreakLabel =
             error "Ivory.Language.Coroutine: no break label set, but breakOut called"
           }

  initialState = CoroutineState
                 { rewrites = Map.empty
                 , labels = []
                 , derefs = 0
                 }

  -- Even the initial block needs a label, in case there's a yield or
  -- return before any control flow statements. Otherwise, the resulting
  -- resumeAt call will emit a 'break;' statement outside of the
  -- forever-loop that the state machine runs in, which is invalid C.
  initCode = makeLabel' =<< getBlock rawCode (resumeAt 0)
  (((initLabel, _), (localVars, resumes)), finalState) =
     MonadLib.runM initCode params initialState
  initBB = BasicBlock [] $ BranchTo False initLabel

  coroutineType :: AST.Type
  coroutineType = ivoryArea (Proxy :: Proxy a)

  -- | Return continuation is: ProcPtr ([a] :-> r)]
  returnContType :: AST.Type
  returnContType = AST.TyProc AST.TyVoid [coroutineType]

  -- | Name of the continuation struct type:
  strName = name ++ "_continuation"

  -- | Definitions of the continuation struct type:
  strDef = AST.Struct strName $
           -- State variable:
           AST.Typed stateType stateName :
           -- Return continuation:
           AST.Typed returnContType returnContName :
           D.toList localVars
  strTy = AST.TyStruct strName

  -- | Area for the continuation struct instance:
  contArea = AST.Area (name ++ "_cont") False strTy AST.InitZero

  coroutineName = name

  litLabel = AST.ExpLit . AST.LitInteger . fromIntegral

  genBB (BasicBlock pre term) = pre ++ case term of
    BranchTo suspend label -> (AST.Store stateType (getCont params stateName) $ litLabel label) : if suspend then [AST.Break] else []
    CondBranchTo cond tb fb -> [AST.IfTE cond (genBB tb) (genBB fb)]

  coroutineRun :: IBool -> ConstRef s a -> Ivory eff ()
  coroutineRun doInit arg = do
    ifte_ doInit (emits mempty { blockStmts = genBB initBB }) (return ())
    emit $ AST.Forever $ (AST.Deref stateType (AST.VarName stateName) $ getCont params stateName) : do
      (label, block) <- keepUsedBlocks initLabel $ zip [0..] $ map joinTerminators $ (BasicBlock [] $ BranchTo True 0) : reverse (labels finalState)
      let cond = AST.ExpOp (AST.ExpEq stateType)
                 [AST.ExpVar (AST.VarName stateName), litLabel label]
          fn :: AST.Expr -> [AST.Stmt]
          fn = Map.findWithDefault (const []) label resumes
          b' = fn (unwrapExpr arg) ++ genBB block
      return $ AST.IfTE cond b' []

  coroutineDef = do
    visibility <- MonadLib.ask
    MonadLib.put $ mempty
      { AST.modStructs = visAcc visibility strDef
      , AST.modAreas = visAcc visibility contArea
      }

-- | This is used as the name of a pseudo-function call which marks the
-- 'yield' in a coroutine.  It is purposely not a valid C identifier so that
-- it can't collide with a real procedure.
yieldName :: String
yieldName = "+yield"

-- | Name of the return continuation function
returnContName :: String
returnContName = "ret_cont"

-- | Name of the variable used for the coroutine's current state.
stateName :: String
stateName = "state"

-- | The type used for the continuation's state.
stateType :: AST.Type
stateType = AST.TyWord AST.Word32

data BasicBlock = BasicBlock AST.Block Terminator
type Goto = Int
data Terminator
  = BranchTo Bool Goto
  | CondBranchTo AST.Expr BasicBlock BasicBlock

joinTerminators :: BasicBlock -> BasicBlock
joinTerminators (BasicBlock b (CondBranchTo cond t f)) =
  case (joinTerminators t, joinTerminators f) of
  (BasicBlock bt (BranchTo yt lt), BasicBlock bf (BranchTo yf lf))
    | yt == yf && lt == lf -> BasicBlock (b ++ [AST.IfTE cond bt bf]) (BranchTo yt lt)
  (t', f') -> BasicBlock b (CondBranchTo cond t' f')
joinTerminators bb = bb

doInline :: Goto -> [(Goto, BasicBlock)] -> [(Goto, BasicBlock)]
doInline inlineLabel blocks = do
  let Just (BasicBlock newStmts tgt) = lookup inlineLabel blocks
  let inlineBlock (BasicBlock b (BranchTo False dst))
        | dst == inlineLabel = BasicBlock (b ++ newStmts) tgt
      inlineBlock (BasicBlock b (CondBranchTo cond tb fb))
        = joinTerminators $ BasicBlock b $ CondBranchTo cond (inlineBlock tb) (inlineBlock fb)
      inlineBlock bb = bb
  (label, bb) <- blocks
  return $ if label == inlineLabel then (label, bb) else (label, inlineBlock bb)

keepUsedBlocks :: Goto -> [(Goto, BasicBlock)] -> [(Goto, BasicBlock)]
keepUsedBlocks root blocks = sweep $ snd $ MonadLib.runM (mark root >> ref root) IntMap.empty
  where
  mark :: Goto -> MonadLib.StateT (IntMap.IntMap Int) MonadLib.Id ()
  mark label = do
    seen <- MonadLib.get
    ref label
    unless (label `IntMap.member` seen) $ do
      let Just b = lookup label blocks
      markBlock b
  ref label = MonadLib.sets_ $ IntMap.insertWith (+) label 1
  markBlock (BasicBlock _ (BranchTo suspend label)) = do
    mark label
    -- add an extra reference for yield targets
    when suspend $ ref label
  markBlock (BasicBlock _ (CondBranchTo _ tb fb)) = markBlock tb >> markBlock fb
  sweep used = filter (\ (label, _) -> IntMap.findWithDefault 0 label used > 1) $
    foldr doInline blocks [ label | (label, 1) <- IntMap.assocs used ]

data CoroutineParams = CoroutineParams
  { getCont :: String -> AST.Expr
  , getBreakLabel :: Terminator
  }

data CoroutineState = CoroutineState
  { rewrites :: Map.Map AST.Var (CoroutineMonad AST.Expr)
  , labels :: [BasicBlock]
  , derefs :: !Integer
  }

type CoroutineResume = Map.Map Goto (AST.Expr -> AST.Block)

type CoroutineVars = (D.DList (AST.Typed String), CoroutineResume)

type CoroutineMonad = MonadLib.WriterT
                      (D.DList AST.Stmt)
                      (MonadLib.ReaderT CoroutineParams
                       (MonadLib.WriterT CoroutineVars
                        (MonadLib.StateT CoroutineState MonadLib.Id)))

-- | Walk an 'AST.Stmt', update its variables as necessary to refer to the
-- continuation struct, and any time a new local is introduced, add it to the
-- continuation struct.
extractLocals :: AST.Stmt
                 -> CoroutineMonad Terminator
                 -> CoroutineMonad Terminator
extractLocals (AST.IfTE cond tb fb) rest = do
  after <- makeLabel rest
  CondBranchTo <$> runUpdateExpr (updateExpr cond)
    <*> getBlock tb (return after)
    <*> getBlock fb (return after)
extractLocals (AST.Assert cond) rest =
  (AST.Assert <$> runUpdateExpr (updateExpr cond)) >>= stmt >> rest
extractLocals (AST.CompilerAssert cond) rest =
  (AST.CompilerAssert <$> runUpdateExpr (updateExpr cond)) >>= stmt >> rest
extractLocals (AST.Assume cond) rest =
  (AST.Assume <$> runUpdateExpr (updateExpr cond)) >>= stmt >> rest
extractLocals (AST.Return {}) _ =
  error "Ivory.Language.Coroutine: can't return a value from the coroutine body"
-- XXX: this discards any code after a return. is that OK?
extractLocals (AST.ReturnVoid) _ = resumeAt 0
extractLocals (AST.Deref ty var ex) rest =
  (AST.RefCopy ty <$> addLocal ty var <*> runUpdateExpr (updateExpr ex)) >>=
  stmt >> rest
  -- Note here that an 'AST.Deref' also emits a 'RefCopy' and another local.
extractLocals (AST.Store ty lhs rhs) rest =
  (runUpdateExpr $ AST.Store ty <$> updateExpr lhs <*> updateExpr rhs) >>=
  stmt >> rest
extractLocals (AST.Assign ty var ex) rest =
  (AST.Store ty <$> addLocal ty var <*> runUpdateExpr (updateExpr ex)) >>=
  stmt >> rest
extractLocals (AST.Call ty mvar name args) rest
  -- 'yieldName' is the pseudo-function call which we handle specially at this
  -- point using 'addYield':
  | name == AST.NameSym yieldName = do
      -- XXX: yield takes no arguments and always returns something
      let (Just var, []) = (mvar, args)
      addYield ty var rest
  | otherwise = do
      -- All other function calls pass through normally, but have their
      -- arguments run through 'updateTypedExpr' and have their results saved
      -- into the continuation:
      stmt =<< AST.Call ty mvar name <$>
        runUpdateExpr (mapM updateTypedExpr args)
      case mvar of
       Nothing -> return ()
       Just var -> do
         cont <- addLocal ty var
         stmt $ AST.Store ty cont $ AST.ExpVar var
      rest
extractLocals (AST.Local ty var initex) rest = do
  cont <- addLocal ty var
  let AST.VarName varStr = var
  let ref = AST.VarName $ varStr ++ "_ref"
  initex' <- runUpdateExpr $ updateInit initex
  stmts
    [ AST.Local ty var initex'
    , AST.AllocRef ty ref $ AST.NameVar var
    , AST.RefCopy ty cont $ AST.ExpVar ref
    ]
  rest
extractLocals (AST.RefCopy ty lhs rhs) rest =
  (runUpdateExpr $ AST.RefCopy ty <$> updateExpr lhs <*> updateExpr rhs) >>=
  stmt >> rest
extractLocals (AST.AllocRef _ty refvar name) rest = do
  let AST.NameVar var = name -- XXX: AFAICT, AllocRef can't have a NameSym argument.
  refvar `rewriteTo` contRef var
  rest
extractLocals (AST.Loop var initEx incr b) rest = do
  let ty = ivoryType (Proxy :: Proxy IxRep)
  cont <- addLocal ty var
  stmt =<< AST.Store ty cont <$> runUpdateExpr (updateExpr initEx)
  after <- makeLabel rest
  mfix $ \ loop -> makeLabel $ do
    let (condOp, incOp, limitEx) = case incr of
          AST.IncrTo ex -> (AST.ExpGt, AST.ExpAdd, ex)
          AST.DecrTo ex -> (AST.ExpLt, AST.ExpSub, ex)
    cond <- runUpdateExpr $ updateExpr $
            AST.ExpOp (condOp False ty) [AST.ExpVar var, limitEx]
    CondBranchTo cond (BasicBlock [] after) <$> do
      setBreakLabel after $ getBlock b $ do
        stmt =<< AST.Store ty cont <$>
          runUpdateExpr (updateExpr $ AST.ExpOp incOp
                         [AST.ExpVar var, AST.ExpLit (AST.LitInteger 1)])
        return loop
extractLocals (AST.Forever b) rest = do
  after <- makeLabel rest
  mfix $ \ loop -> makeLabel $ setBreakLabel after $
                   foldr extractLocals (return loop) b
-- XXX: this discards any code after a break. is that OK?
extractLocals (AST.Break) _ = MonadLib.asks getBreakLabel
extractLocals s@(AST.Comment{}) rest = stmt s >> rest

getBlock :: AST.Block -> CoroutineMonad Terminator -> CoroutineMonad BasicBlock
getBlock b next = do
  (term, b') <- MonadLib.collect $ foldr extractLocals next b
  return $ BasicBlock (D.toList b') term

makeLabel :: CoroutineMonad Terminator -> CoroutineMonad Terminator
makeLabel m = do
  block <- getBlock [] m
  case block of
    BasicBlock b term | all isComment b -> do
      stmts b
      return term
    _ -> goto =<< makeLabel' block
  where
  isComment (AST.Comment{}) = True
  isComment _ = False

makeLabel' :: BasicBlock -> CoroutineMonad Goto
makeLabel' block = MonadLib.sets $ \ state ->
  let state' = state { labels = block : labels state }
  in (length (labels state'), state')

goto :: Goto -> CoroutineMonad Terminator
goto = return . BranchTo False

resumeAt :: Goto -> CoroutineMonad Terminator
resumeAt = return . BranchTo True

contRef :: AST.Var -> CoroutineMonad AST.Expr
contRef var = do
  let AST.VarName varStr = var
  MonadLib.asks getCont <*> pure varStr

addLocal :: AST.Type -> AST.Var -> CoroutineMonad AST.Expr
addLocal ty var = do
  let AST.VarName varStr = var
  MonadLib.lift $ MonadLib.put (D.singleton $ AST.Typed ty varStr, mempty)
  cont <- contRef var
  var `rewriteTo` do
    idx <- MonadLib.sets $ \ state -> (derefs state, state { derefs = derefs state + 1 })
    let var' = AST.VarName $ "cont" ++ show idx
    stmt $ AST.Deref ty var' cont
    return $ AST.ExpVar var'
  return cont

-- | Generate the code to turn a @yield@ pseudo-call to a suspend and resume.
addYield :: AST.Type -> AST.Var -> CoroutineMonad Terminator ->
            CoroutineMonad Terminator
addYield ty var rest = do
  let AST.TyRef derefTy = ty
      AST.VarName varStr = var
  MonadLib.lift $ MonadLib.put
    (D.singleton $ AST.Typed derefTy varStr, mempty)
  cont <- contRef var
  var `rewriteTo` return cont
  after <- makeLabel' =<< getBlock [] rest
  let resume arg = [AST.RefCopy derefTy cont arg]
  MonadLib.lift $ MonadLib.put (mempty, Map.singleton after resume)
  resumeAt after

-- | Generate the code to turn a @yieldTo@ pseudo-call to yielding control to
-- another coroutine, and the subsequent resume.
addYieldTo :: AST.Type -> AST.Var -> CoroutineMonad Terminator ->
            CoroutineMonad Terminator
addYieldTo ty var rest = do
  let AST.TyRef derefTy = ty
      AST.VarName varStr = var
  MonadLib.lift $ MonadLib.put
    (D.singleton $ AST.Typed derefTy varStr, mempty)
  -- Capture/rewrite the return of the yield:
  -- (this should be the same with yield or yieldTo, right?)
  cont <- contRef var
  var `rewriteTo` return cont
  -- CMH: Set the return continuation?
  -- I need to get somehow into the continuation of what we're invoking,
  -- not our own continuation.  This may enforce a dependency between modules,
  -- as it must be able to see the variable.  (But, I suppose this is
  -- no big deal.)
  -- Inside of 'coroutine' is contArea which is this struct itself as an
  -- AST.Area.  I could factor this out into a function parametrized over
  -- the coroutine or coroutine name.
  -- returnCont <- MonadLib.asks getCont <*> pure returnContName
  after <- makeLabel' =<< getBlock [] rest
  let resume arg = [AST.RefCopy derefTy cont arg]
  MonadLib.lift $ MonadLib.put (mempty, Map.singleton after resume)
  resumeAt after

setBreakLabel :: Terminator -> CoroutineMonad a -> CoroutineMonad a
setBreakLabel label m = do
  params <- MonadLib.ask
  MonadLib.local (params { getBreakLabel = label }) m

-- | Insert a statement into a 'CoroutineMonad'.
stmt :: AST.Stmt -> CoroutineMonad ()
stmt s = MonadLib.put $ D.singleton s

-- | Insert a block of statements into a 'CoroutineMonad'.
stmts :: AST.Block -> CoroutineMonad ()
stmts = MonadLib.put . D.fromList

-- | Inside of a 'CoroutineMonad', rewrite the given variable name to the
-- contained expression.
rewriteTo :: AST.Var -> CoroutineMonad AST.Expr -> CoroutineMonad ()
rewriteTo var repl =
  MonadLib.sets_ $ \state -> state
                             { rewrites = Map.insert var repl $ rewrites state }

-- | State monad containing a map of updates from variables to expressions
-- (typically for the sake of updating variable references to refer instead to
-- the continuation struct).
type UpdateExpr a = MonadLib.StateT (Map.Map AST.Var AST.Expr) CoroutineMonad a

-- | Apply the given variable updates
runUpdateExpr :: UpdateExpr a -> CoroutineMonad a
runUpdateExpr = fmap fst . MonadLib.runStateT Map.empty

-- | Updates variable references in the supplied expression (as well as
-- recursively to all sub-expressions) with the updates in 'UpdateExpr'.
updateExpr :: AST.Expr -> UpdateExpr AST.Expr
updateExpr ex@(AST.ExpVar var) = do
  updated <- MonadLib.get
  case Map.lookup var updated of
    Just ex' -> return ex'
    Nothing -> do
      ex' <- MonadLib.lift $ do
        Map.findWithDefault (return ex) var =<< fmap rewrites MonadLib.get
      MonadLib.sets_ $ Map.insert var ex'
      return ex'
updateExpr (AST.ExpLabel ty ex label) =
  AST.ExpLabel ty <$> updateExpr ex <*> pure label
updateExpr (AST.ExpIndex ty1 ex1 ty2 ex2) =
  AST.ExpIndex <$> pure ty1 <*> updateExpr ex1 <*> pure ty2 <*> updateExpr ex2
updateExpr (AST.ExpToIx ex bound) =
  AST.ExpToIx <$> updateExpr ex <*> pure bound
updateExpr (AST.ExpSafeCast ty ex) =
  AST.ExpSafeCast ty <$> updateExpr ex
updateExpr (AST.ExpOp op args) =
  AST.ExpOp op <$> mapM updateExpr args
updateExpr ex = return ex

-- | Update an initializer with the variable replacements in the given
-- 'UpdateExpr'
updateInit :: AST.Init -> UpdateExpr AST.Init
updateInit AST.InitZero = return AST.InitZero
updateInit (AST.InitExpr ty ex) =
  -- 'AST.InitExpr' contains an expression that 'updateExpr' needs to handle:
  AST.InitExpr ty <$> updateExpr ex
updateInit (AST.InitStruct fields) =
  -- Every field of a @struct@ in an 'AST.InitStruct' contains an expression
  -- that must go through 'updateExpr':
  AST.InitStruct <$> mapM (\ (name, ex) -> (,) name <$> updateInit ex) fields
updateInit (AST.InitArray elems) =
  -- An 'AST.InitArray' is a list of 'AST.Init' which we must recurse over:
  AST.InitArray <$> mapM updateInit elems

-- | Update variable references in the supplied typed expression (and
-- recursively in all its sub-expressions) with the updates in 'UpdateExpr'.
updateTypedExpr :: AST.Typed AST.Expr -> UpdateExpr (AST.Typed AST.Expr)
updateTypedExpr (AST.Typed ty ex) = AST.Typed ty <$> updateExpr ex


-- * Experimental stuff with composition

{- Dabbling notes

- At the C level, 'yield' causes the function to return.
- Though it has some first-class status in Haskell, it cannot be passed around
as a value.
- The results of a 'yield', however, can be passed.
- One can use 'yield' to pass a ProcPtr using my changes.
- Neither calling that ProcPtr directly, nor passing it as an argument to
another call, can ever have the same effect as 'yield'.  These are always
normal function calls, and however many times they pass values forward in
continuation-passing style, all of them must at some point return.
- This fact, combined with the behavior of 'yield' suggests to me that I do
*not* have continuations here in the form I was hoping!  What I possibly have
is coroutines that can compose.

In some sense, the 'yield' action sets up the continuation for the function
in which it is called.  That continuation is accessed via 'coroutineRun'.

What, then, does a ProcPtr passed at the point of continuation correspond
to? The ProcPtr itself still appears to be like the 'continuation object',
in which calling it is its only meaningful operation.

If I must pass this continuation object to the point of continuation, there
is one way to do this: with an existing 'coroutineRun'.  This is also one
way that I see of getting a compatible ProcPtr in the first place.

Suppose I have coroutines A, B, and C, and I want coroutines A and B to both be
able to invoke coroutine C, but properly have coroutine C turn control back
over to A or B depending on who called it.  For this to work, coroutine C must
have some notion of who invoked it - and the most general way that I see of
this working is for coroutine C to receive some sort of continuation.  Like
mentioned before, a 'return' ProcPtr can be seen as one representation of the
continuation.  (This example still has some gotchas: You cannot have two
instances of coroutine C running simultaneously.)

Mainly, one can now resume a function, *and* supply a continuation to which to
pass a value eventually. Further, this can be done inside of a coroutine
safely, I think.

I suppose I could make an Ivory effect parametrized over two things, make the
first thing the 'return' continuation, and use currying to get this to an
effect taking one argument - which then could be the coroutine body.

Or, I could add this argument to CoroutineBody. This would require two changes:
 - 'coroutineRun' would require an additional argument for which there is no
sensible default - the continuation ProcPtr.
 - All coroutine definitions would require an additional argument alongside
'yield' (though I may be able to just make two smart constructors and leave old
uses of it compatible).

But if it's passed as an additional argument, then what need have I to make
'yield' comprehend it specially?  The coroutine still can store a ProcPtr for
later usage inside its own continuation.  (But, is this any different than just
making 'yield' return 2 parameters, instead of just 1?)

But going to the prior example with coroutines A, B, and C, how could coroutine
C ever pass a value back to coroutine A/B?  It can only pass a function
pointer.  It would have to generate a function which returns something and then
rely on A/B to call it and acquire this result, which hardly seems ideal.

I am also stuck at the ordering of yielding and calling when one wants to call
one coroutine from another.
Coroutine A calls coroutine C, giving its own continuation.  Coroutine C either
finishes immediately (without suspending) and calls that continuation itself,
at which point coroutine A now has two simultaneous instances running.  Its
state has never changed, which means that it just calls coroutine C again - and
presumably, is then caught in an infinite loop.  Or, coroutine C must suspend
itself (perhaps it stores the continuation to A), and this takes the form of
returning.  Coroutine A is then back in control and is free to yield or do
whatever it must do; presumably, it must yield and change its state so that
once coroutine C is resumed, it can resume coroutine A.

So, it appears that a callee coroutine must yield, and permit the caller to
yield, and then something else must resume the caller. Or, the caller must have
a way to yield at the same instant as making a call, and then the callee can
resume the caller whether it does it immediately, or whether it first suspends
and is resumed.  This still has some stack implications, but it may not be too
problematic.

This would need some sort of special 'yieldTo' action which suspends the
coroutine, but passes the calling coroutine's continuation to another
coroutine.

This has also let alone the question of what one does to call another coroutine
but specify that that coroutine should turn control to a 3rd coroutine.

-}
