{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Ivory.Language.Coroutine (
  Coroutine(..), CoroutineBody(..), coroutine,
) where

-- CMH, debug
import Debug.Trace

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

data Coroutine a = Coroutine
  { coroutineName :: String
  , coroutineRun :: forall eff s . GetAlloc eff ~ Scope s => IBool -> a -> Ivory eff ()
  , coroutineDef :: ModuleDef
  }

-- If I want to write Coroutine in terms of Continuation, then how do I get
-- that 'ConstRef s a' part when it's in an existential?

newtype CoroutineBody a =
  CoroutineBody (forall s.
                 (forall b.
                  Ivory ('Effects (Returns ()) b (Scope s)) a) ->
                         Ivory (ProcEffects s ()) ())

-- It looks to me like any CoroutineBody is also a ContBody, though I'm not
-- certain.

coroutine :: forall a. IvoryVar a => String -> CoroutineBody a -> Coroutine a
coroutine name (CoroutineBody fromYield) = Coroutine { .. }
  where
  ((), CodeBlock { blockStmts = rawCode }) =
    runIvory $ fromYield $ call (proc yieldName $ body $ return ())
  -- This appears to operate by passing a call to a function called "+yield"
  -- (or yieldName), and this call is then extracted later and replaced.

  -- If I want to do what I discuss elsewhere and have 'yield' actually *be*
  -- a function call, I will need to replace the above placeholder function
  -- with some ProcPtr which will be one of the arguments to the generated
  -- code.
  -- However, then a continuation can be parametrized only over ProcPtr,
  -- and it's doubtful I'll be able to make coroutines a special case of them.
  -- Also, that argument is the 'a' in contRun below, and I'm not sure how
  -- I'd be able to get at that argument from here, or if I even could.
  -- The way I understand it, all my definitions must be parametrized over it,
  -- and it can't escape that.

  -- However, the convention of using the dummy name (+yield) works well
  -- enough.  If I get the type signature right, then I could close the loop
  -- in the AST later (instead of turning this into the dereferences and such).

  -- Why I'm not doing this approach currently is that changing the type of
  -- this pseudo-call is resulting in a world of pain when it comes to type
  -- signatures.

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

  contName = name

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

extractLocals :: AST.Stmt
                 -> CoroutineMonad Terminator
                 -> CoroutineMonad Terminator
extractLocals (AST.IfTE cond tb fb) rest = do
  after <- makeLabel rest
  CondBranchTo <$> runUpdateExpr (updateExpr_ cond)
    <*> getBlock tb (return after)
    <*> getBlock fb (return after)
extractLocals (AST.Assert cond) rest =
  (AST.Assert <$> runUpdateExpr (updateExpr_ cond)) >>= stmt >> rest
extractLocals (AST.CompilerAssert cond) rest =
  (AST.CompilerAssert <$> runUpdateExpr (updateExpr_ cond)) >>= stmt >> rest
extractLocals (AST.Assume cond) rest =
  (AST.Assume <$> runUpdateExpr (updateExpr_ cond)) >>= stmt >> rest
extractLocals (AST.Return {}) _ =
  error "Ivory.Language.Coroutine: can't return a value from the coroutine body"
-- XXX: this discards any code after a return. is that OK?
extractLocals (AST.ReturnVoid) _ = resumeAt 0
extractLocals (AST.Deref ty var ex) rest =
  (AST.RefCopy ty <$> addLocal ty var <*> runUpdateExpr (updateExpr_ ex)) >>=
  stmt >> rest
  -- CMH: Note here that a Deref also emits a RefCopy and another local.
extractLocals (AST.Store ty lhs rhs) rest =
  (runUpdateExpr $ AST.Store ty <$> updateExpr_ lhs <*> updateExpr_ rhs) >>=
  stmt >> rest
extractLocals (AST.Assign ty var ex) rest =
  (AST.Store ty <$> addLocal ty var <*> runUpdateExpr (updateExpr_ ex)) >>=
  stmt >> rest
extractLocals (AST.Call ty mvar name args) rest
  | name == AST.NameSym yieldName = trace "name == AST.NameSym branch" $ do
    let (Just var, []) = (mvar, args) -- XXX: yield takes no arguments and always returns something
    addYield ty var rest
    -- CMH: In this branch the result of that function call is 'assigned' to
    -- a variable name inside the continuation, and it appears to me that this
    -- name makes its way into the returned value somehow.
    -- This assignment does however occur to the continuation struct (and it
    -- looks like addYield takes care of this) with the correct name.
    -- addField receives this name in some form.
    -- The 'indirect_' call then picks up a name that requires mangling but has
    -- never been allocated (nor is the un-mangled name useful).
    -- So, how does the name make its way to the return value?

    -- If I call something else via 'indirect' I see the name emerge as a
    -- NameSym (rather than a NameVar & VarName).

    -- The variable holding the result of the +yield call appears to be out of
    -- sync with what is actually returned to the monad, but what do I change
    -- to get them back in sync?

    -- The normal Ivory coroutines always employ a 'deref' after the yield,
    -- so perhaps is the AST.Deref intercepted and patched in some way?
    -- I see that they add a RefCopy & addLocal there, and indeed I see in
    -- some examples that this generates a new local variable and that
    -- operations are then done on this.

    -- So... is the result of this function call invalid, because no actual
    -- function call exists?  If this is the case then how does it become
    -- valid through a 'deref'?

    -- Further, how can I apply this?  I can't put a 'deref' here - the type
    -- system will not allow it.  What can I modify about this fake function
    -- call, *and* propagate back to the monad?
    -- Is this what 'runUpdateExpr' is for?
  | otherwise = trace "otherwise branch" $ do
    stmt =<< AST.Call ty mvar name <$> runUpdateExpr (mapM updateTypedExpr args)
    -- CMH: updateTypedExpr runs here on the arguments of the function, and it
    -- does not run in the prior branch.
    -- I suppose I could do two things: Run it on the result of the +yield
    -- pseudo-call, or run it on the call that comes after. I cannot tell apart
    -- the call that comes after from any other function call - but does this
    -- matter, if I am only replacing certain variables selectively (according
    -- to what is in the map)?
    -- The normal coroutine code does it on the variable reference that occurs
    -- as a result of the normal operations on the variable - I think?  It
    -- appears to also emit a new variable declaration & definition at the
    -- spot as well.  (I guess that's what the code below does?)
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
  (runUpdateExpr $ AST.RefCopy ty <$> updateExpr_ lhs <*> updateExpr_ rhs) >>=
  stmt >> rest
extractLocals (AST.AllocRef _ty refvar name) rest = do
  let AST.NameVar var = name -- XXX: AFAICT, AllocRef can't have a NameSym argument.
  refvar `rewriteTo` contRef var
  rest
extractLocals (AST.Loop var initEx incr b) rest = do
  let ty = ivoryType (Proxy :: Proxy IxRep)
  cont <- addLocal ty var
  stmt =<< AST.Store ty cont <$> runUpdateExpr (updateExpr_ initEx)
  after <- makeLabel rest
  mfix $ \ loop -> makeLabel $ do
    let (condOp, incOp, limitEx) = case incr of
          AST.IncrTo ex -> (AST.ExpGt, AST.ExpAdd, ex)
          AST.DecrTo ex -> (AST.ExpLt, AST.ExpSub, ex)
    cond <- runUpdateExpr $ updateExpr_ $
            AST.ExpOp (condOp False ty) [AST.ExpVar var, limitEx]
    CondBranchTo cond (BasicBlock [] after) <$> do
      setBreakLabel after $ getBlock b $ do
        stmt =<< AST.Store ty cont <$>
          runUpdateExpr (updateExpr_ $ AST.ExpOp incOp
                         [AST.ExpVar var, AST.ExpLit (AST.LitInteger 1)])
        return loop
extractLocals (AST.Forever b) rest = do
  after <- makeLabel rest
  mfix $ \ loop -> makeLabel $ setBreakLabel after $
                   foldr extractLocals_ (return loop) b
-- XXX: this discards any code after a break. is that OK?
extractLocals (AST.Break) _ = MonadLib.asks getBreakLabel
extractLocals s@(AST.Comment{}) rest = stmt s >> rest

-- CMH
extractLocals_ :: AST.Stmt -> CoroutineMonad Terminator -> CoroutineMonad Terminator
extractLocals_ a = trace ("extractLocals: " ++ show a) $ extractLocals a

getBlock :: AST.Block -> CoroutineMonad Terminator -> CoroutineMonad BasicBlock
getBlock b next = do
  (term, b') <- MonadLib.collect $ foldr extractLocals_ next b
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
addYield ty var rest =
  trace ("addYield ty=" ++ show ty ++ ", var=" ++ show var) $ do
  case ty of (AST.TyRef derefTy) -> do
               let AST.VarName varStr = var
               MonadLib.lift $ MonadLib.put
                 (D.singleton $ AST.Typed derefTy varStr, mempty)
               cont <- contRef var
               var `rewriteTo` return cont
               after <- makeLabel' =<< getBlock [] rest
               let resume arg = [AST.RefCopy derefTy cont arg]
               MonadLib.lift $ MonadLib.put
                 (mempty, Map.singleton after resume)
               resumeAt after
             (AST.TyConstRef derefTy) -> addYield (AST.TyRef derefTy) var rest
             (AST.TyProc r args) -> do
               -- The argument to TyProc appears to just be void type (which is
               -- not useful to us), however, the above pattern match works.
               {-
               let AST.VarName varStr = var
               MonadLib.lift $ MonadLib.put
                 (D.singleton $ AST.Typed ty varStr, mempty)

               -}
               -- Responsible for n_r0(?):
               -- cont <- contRef var
               -- Responsible for ????:
               -- var `rewriteTo` return cont

               after <- makeLabel' =<< getBlock [] rest

               -- Responsible for copying value (do we even need this?):
               let resume arg = [AST.Local ty var $ AST.InitExpr ty $ arg]
               
               MonadLib.lift $ MonadLib.put (mempty, Map.singleton after resume)

               -- stmt $ 
               --stmt $ AST.Call r Nothing (AST.NameVar var) []
               -- CMH, TODO: Fix Nothing (need to store result)
               -- Big TODO: The arguments are incorrect on this. I will need
               -- to update the type signature of the function that is passed
               -- for 'yield'.
               -- I suspect this function cannot accomplish what I need, but
               -- the calling context does contains the arguments.
               
               resumeAt after

               -- If I am calling this ProcPtr separately then I don't think I
               -- can do anything in this branch - I have to correct the name
               -- elsewhere.
               -- 
               -- But what about if I insert a call directly here?  This would
               -- change semantics somewhat.  But would it matter?  The
               -- Haskell code can still pass it around as a first-class value,
               -- but it cannot store it in a C variable, only pass it to other
               -- continuations.
               -- I see two potential problems: How would I get the return
               -- value of the continuation, and how would I pass values to it?
               -- These are both trivial if I have a ProcPtr which I call with
               -- 'indirect'.
               -- However, to do this without 'indirect' I would have to
               -- fundamentally change the type of 'yield' that is passed to
               -- the function for the psuedo-call in order for it to
               -- comprehend arguments and return values.
               -- That *might* be doable. I could change the signature of the
               -- pseudo-call based on what the ProcPtr is parametrized over,
               -- then it would be a matter of changing its name to properly
               -- reflect the function that was passed in.  (And that would
               -- be constant: It's one of the function arguments.)
               -- This breaks from how Coroutine works, in which the
               -- pseudo-call signature is unconnected to the type of the
               -- coroutine itself.  But is that much of an issue?

setBreakLabel :: Terminator -> CoroutineMonad a -> CoroutineMonad a
setBreakLabel label m = do
  params <- MonadLib.ask
  MonadLib.local (params { getBreakLabel = label }) m

stmt :: AST.Stmt -> CoroutineMonad ()
stmt s = trace ("stmt " ++ show s) $ MonadLib.put $ D.singleton s

stmts :: AST.Block -> CoroutineMonad ()
stmts = MonadLib.put . D.fromList

-- | Inside of a 'CoroutineMonad', rewrite the given variable name to the
-- contained expression.
rewriteTo :: AST.Var -> CoroutineMonad AST.Expr -> CoroutineMonad ()
rewriteTo var repl =
  MonadLib.sets_ $ \state -> state
                             { rewrites = Map.insert var repl $ rewrites state }

type UpdateExpr a = MonadLib.StateT (Map.Map AST.Var AST.Expr) CoroutineMonad a

-- | Apply the given variable updates
runUpdateExpr :: UpdateExpr a -> CoroutineMonad a
runUpdateExpr = fmap fst . MonadLib.runStateT Map.empty

-- CMH
updateExpr_ :: AST.Expr -> UpdateExpr AST.Expr
updateExpr_ a = trace ("updateExpr " ++ show a) $ updateExpr a

-- CMH: updateExpr seems to update an expression in the AST with some
-- replacements.  If I'm reading that right, it does so with the Map that is
-- in UpdateExpr.  This appears to be just a recursive application of
-- updateExpr in all sub-expressions - except for with AST.ExpVar, which looks
-- up replacements in 'UpdateExpr'.
-- This never appears to run on 'indirect' - only on 'deref'.  I believe
-- 'extractLocals' never runs it on AST.Call.  And it would do us no good -
-- it inspects expressions, but AST.Call is a statement, not an expression, and
-- it contains no expressions that require updating - only a result variable
-- and a name.
-- I could replace one of those variables according to the map, but I'd be
-- replacing it with an expression - and I can't call an expression, or assign
-- to one.  So, an updateCall counterpart wouldn't be readily usable.
--
-- The basic disconnect here appears to be that 'AST.Deref' operates on
-- expressions, and this code can handle updating expressions, but 'AST.Call'
-- operates on variables or variable names.
-- I could perhaps allocate a Local to address this and initialize it with an
-- InitExpr and the Expr in question.
--
-- This has the problem of generating unnecessary locals for every single
-- function call though, unless we only generate a local if the map contains
-- a replacement expression.
updateExpr :: AST.Expr -> UpdateExpr AST.Expr
updateExpr ex@(AST.ExpVar var) = do
  updated <- MonadLib.get
  case Map.lookup var updated of
    Just ex' -> trace ("  updateExpr: unchanged AST.ExpVar") $ return ex'
    Nothing -> do
      ex' <- MonadLib.lift $ do
        Map.findWithDefault (return ex) var =<< fmap rewrites MonadLib.get
      MonadLib.sets_ $ Map.insert var ex'
      trace ("  updateExpr: new " ++ show ex') $ return ex'
updateExpr (AST.ExpLabel ty ex label) =
  AST.ExpLabel ty <$> updateExpr_ ex <*> pure label
updateExpr (AST.ExpIndex ty1 ex1 ty2 ex2) =
  AST.ExpIndex <$> pure ty1 <*> updateExpr_ ex1 <*> pure ty2 <*> updateExpr_ ex2
updateExpr (AST.ExpToIx ex bound) =
  AST.ExpToIx <$> updateExpr_ ex <*> pure bound
updateExpr (AST.ExpSafeCast ty ex) =
  AST.ExpSafeCast ty <$> updateExpr_ ex
updateExpr (AST.ExpOp op args) =
  AST.ExpOp op <$> mapM updateExpr_ args
updateExpr ex = return ex

-- | Update an initializer with the variable replacements in the given
-- 'UpdateExpr'
updateInit :: AST.Init -> UpdateExpr AST.Init
updateInit AST.InitZero = return AST.InitZero
updateInit (AST.InitExpr ty ex) =
  -- 'AST.InitExpr' contains an expression that 'updateExpr' needs to handle:
  AST.InitExpr ty <$> updateExpr_ ex
updateInit (AST.InitStruct fields) =
  -- Every field of a @struct@ in an 'AST.InitStruct' contains an expression
  -- that must go through 'updateExpr':
  AST.InitStruct <$> mapM (\ (name, ex) -> (,) name <$> updateInit ex) fields
updateInit (AST.InitArray elems) =
  -- An 'AST.InitArray' is a list of 'AST.Init' which we must recurse over:
  AST.InitArray <$> mapM updateInit elems

updateTypedExpr :: AST.Typed AST.Expr -> UpdateExpr (AST.Typed AST.Expr)
updateTypedExpr (AST.Typed ty ex) =
  trace ("updateTypedExpr AST.Typed ty=" ++ show ty ++ ", ex=" ++ show ex) $
  AST.Typed ty <$> updateExpr_ ex
