{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Coroutine where

import Ivory.Language
import Ivory.Compile.C.CmdlineFrontend

-- No-op "action" for the coroutine to trigger
emit :: Def ('[Sint32] :-> ())
emit = proc "emit" $ \ _ -> body $ retVoid

sequenced :: Coroutine (Stored Sint32)
sequenced = coroutine "sequenced" $ CoroutineBody $ \yield yieldTo yieldFrom -> do
  forever $ do
    call_ emit 1
    v <- yieldTo sequenced2 >>= deref
    ifte_ (v ==? 1) breakOut (return ())
  call_ emit 2
  forever $ do
    v <- yield >>= deref
    ifte_ (v ==? 2)
      (call_ emit 3)
      (call_ emit 2)

sequenced2 :: Coroutine (Stored Sint32)
sequenced2 = coroutine "sequenced2" $ CoroutineBody $ \yield yieldTo yieldFrom -> do
  forever $ do
    call_ emit 1
    v <- yield >>= deref
    ifte_ (v ==? 1) breakOut (return ())
  call_ emit 2
  forever $ do
    v <- yield >>= deref
    ifte_ (v ==? 2)
      (call_ emit 3)
      (call_ emit 2)

run :: Def ('[IBool, ConstRef s (Stored Sint32)] :-> ())
run = proc "run" $ \ doInit arg -> body $ coroutineRun sequenced doInit arg

cmodule :: Module
cmodule = package "sequenced" $ do
  incl emit
  incl run
  coroutineDef sequenced
  coroutineDef sequenced2

main :: IO ()
main = runCompiler [cmodule] [] $ initialOpts { scErrors = False
                                              , srcLocs = True
                                              , outDir = Nothing
                                              }
