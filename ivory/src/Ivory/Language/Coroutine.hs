{- |
Module: Coroutine.hs
Description: Resumable coroutines implementation
Copyright: (c) 2014 Galois, Inc.

This is an implementation of coroutines in Ivory.  These coroutines:

  * may be suspended and resumed,
  * are parametrized over most Ivory types,
  * cannot return values, but can receive values when they are resumed,
  * can have only one instance executing at once, given a particular coroutine
name and Ivory module.

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
  Coroutine_(..), ContDef(..), coroutineDef_
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

The pseudo-function call returns a type which relates to the type of the
coroutine itself.  Of course, no actual function call exists, but the action
itself still returns something - hence, Ivory code is able to refer to the
return value of a @yield@.

Dereferences to it via 'deref' are turned to references to the continuation
struct.  (CMH: Explain better here, as this depends on whether or not my change
is present which also turns permits a 'ProcPtr' inside and handles specially
a call using 'indirect' on it.)

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
  , coroutineRun :: forall eff s .
                    GetAlloc eff ~ Scope s => IBool -> a -> Ivory eff ()
    -- | The components a 'Module' will need for this coroutine
  , coroutineDef :: ModuleDef
  }

-- | The definition of a coroutine body, in the form of a function taking one
-- argument: an Ivory effect that is the @yield@ action which suspends the
-- coroutine, and sets the point at which 'coroutineRun' resumes it, passing a
-- value.
newtype CoroutineBody a =
  CoroutineBody (forall s.
                 (forall b.
                  Ivory ('Effects (Returns ()) b (Scope s)) a) ->
                         Ivory (ProcEffects s ()) ())

-- | Smart constructor for a 'Coroutine'
coroutine :: forall a. IvoryVar a =>
             String -- ^ Coroutine name (must be a valid C identifier)
             -> CoroutineBody a -- ^ Coroutine definition
             -> Coroutine a
coroutine name (CoroutineBody fromYield) = Coroutine { .. }
  where
  ((), CodeBlock { blockStmts = rawCode }) =
    runIvory $ fromYield $ call (proc yieldName $ body $ return ())
  -- The above 'call (proc yieldName ...)' is a pseudo-call, returning type
  -- 'a', that is later extracted in the AST and replaced.

  params = CoroutineParams
           { getCont = AST.ExpLabel strTy $ AST.ExpAddrOfGlobal $ AST.areaSym cont
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

  strName = name ++ "_continuation"
  strDef = AST.Struct strName $ AST.Typed stateType stateName :
           D.toList localVars
  strTy = AST.TyStruct strName
  cont = AST.Area (name ++ "_cont") False strTy AST.InitZero

  coroutineName = name

  litLabel = AST.ExpLit . AST.LitInteger . fromIntegral

  genBB (BasicBlock pre term) = pre ++ case term of
    BranchTo suspend label -> (AST.Store stateType (getCont params stateName) $ litLabel label) : if suspend then [AST.Break] else []
    CondBranchTo cond tb fb -> [AST.IfTE cond (genBB tb) (genBB fb)]

  coroutineRun :: IBool -> a -> Ivory eff ()
  coroutineRun doInit arg = do
    ifte_ doInit (emits mempty { blockStmts = genBB initBB }) (return ())
    emit $ AST.Forever $ (AST.Deref stateType (AST.VarName stateName) $ getCont params stateName) : do
      (label, block) <- keepUsedBlocks initLabel $ zip [0..] $ map joinTerminators $ (BasicBlock [] $ BranchTo True 0) : reverse (labels finalState)
      let cond = AST.ExpOp (AST.ExpEq stateType) [AST.ExpVar (AST.VarName stateName), litLabel label]
      let b' = Map.findWithDefault (const []) label resumes (unwrapExpr arg) ++ genBB block
      return $ AST.IfTE cond b' []

  coroutineDef = do
    visibility <- MonadLib.ask
    MonadLib.put $ mempty
      { AST.modStructs = visAcc visibility strDef
      , AST.modAreas = visAcc visibility cont
      }

-- | This is used as the name of a pseudo-function call which marks the
-- 'yield' in a coroutine.  It is purposely not a valid C identifier so that
-- it can't collide with a real procedure.
yieldName :: String
yieldName = "+yield"

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

addYield :: AST.Type -> AST.Var -> CoroutineMonad Terminator -> CoroutineMonad Terminator
addYield (AST.TyRef derefTy) var rest = do
  let AST.VarName varStr = var
  MonadLib.lift $ MonadLib.put
    (D.singleton $ AST.Typed derefTy varStr, mempty)
  cont <- contRef var
  var `rewriteTo` return cont
  after <- makeLabel' =<< getBlock [] rest
  let resume arg = [AST.RefCopy derefTy cont arg]
  MonadLib.lift $ MonadLib.put (mempty, Map.singleton after resume)
  resumeAt after
addYield (AST.TyConstRef t) var rest = addYield (AST.TyRef t) var rest
addYield ty@(AST.TyProc _ args) var rest = do
  after <- makeLabel' =<< getBlock [] rest
  -- At the point of resume, we must copy the argument to a form that function
  -- calls can use:
  -- TODO: Must this be live across a resume too?
  let resume arg = [AST.Local ty var $ AST.InitExpr ty $ arg]
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
continuation.

I suppose I could make an Ivory effect parametrized over two things, make the
first thing the 'return' continuation, and use currying to get this to an
effect taking one argument - which then could be the coroutine body.

-}

-- | A continuation, in the form of a function which produces a 'Coroutine',
-- given its own continuation procedure. (The parameter to the coroutine itself
-- is a pointer to the 'return' continuation.)
type Coroutine_ p = Def ('[ProcPtr p] ':-> ()) -> Coroutine (ProcPtr p)

-- | Experimental continuation-passing coroutines (or something close to that).
-- I explain this, or attempt to, in my work notes around 2015-06-10.
data ContDef p = ContDef {
  -- | Coroutine entry (initialization) procedure.
  contStart :: Def ('[] ':-> ()),
  
  -- | Procedure to continue a coroutine. The argument is a continuation which
  -- this coroutine calls to yield control.
  -- This is something of an analog to 'callCC' on Ivory procedures.
  -- (is it?)
  contCC :: Def ('[ProcPtr p] ':-> ()),
  
  -- | Coroutine definition (do I need this?)
  coDef :: Coroutine (ProcPtr p),

  -- | 'incl' and 'coroutineDef' for the functionality in this
  contModuleDefs :: ModuleDef
}

-- | 'ContDef' smart constructor from a 'Coroutine_'
coroutineDef_ :: forall p ret .
            (ProcType p, IvoryVar (ProcPtr p)) => Coroutine_ p -> ContDef p
coroutineDef_ coFn = ContDef { contStart = start
                       , contCC = contCC_
                       , coDef = coroutine_
                       , contModuleDefs = mods
                       }
  where coroutine_ = coFn contCC_
        name = coroutineName coroutine_

        {-
        -- Function which is just a placeholder:
        dummy :: Def (t ':-> ())
        dummy = proc (name ++ "_dummy") _
        -- The problem is that the next argument in 'dummy' (currently just an
        -- underscore) must take a number of arguments that matches the pattern
        -- of arguments in 't', and I have no idea how to do this.
        -- For now I'm using 'importProc' in 'start' and referring to a made-up
        -- function.
        -}

        start = proc (name ++ "_start") $ body $ do
          -- The coroutine ignores this parameter, but we must pass something:
          call_ impl true $ procPtr $ importProc "dummy" "dummy.h"
          
        contCC_ = proc (name ++ "_cont") $ \cc -> body $ do
          call_ impl true cc

        impl :: Def ('[IBool, ProcPtr p] ':-> ())
        impl = proc (name ++ "_impl") $ \init exit -> body $ do
                     --exit' <- local $ ival exit
                     coroutineRun coroutine_ init exit

        mods = do coroutineDef coroutine_
                  incl start
                  incl impl
                  --incl dummy
