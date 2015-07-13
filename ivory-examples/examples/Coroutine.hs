{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Coroutine where

import Ivory.Language
import Ivory.Compile.C.CmdlineFrontend

-- No-op "action" for the coroutine to trigger
emit :: Def ('[Sint32] :-> ())
emit = proc "emit" $ \ _ -> body $ retVoid

sequenced :: Coroutine (ConstRef s (Stored Sint32))
sequenced = coroutine "sequenced" $ CoroutineBody $ \ yield -> do
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

main :: IO ()
main = compile [cmodule] []

-- * Other tests (to be cleaned up later):

testRun :: IO ()
testRun = do
  let ivoryOpts = initialOpts { scErrors = False
                              , srcLocs = True
                              , outDir = Nothing
                              }
  runCompiler [test] [] ivoryOpts

test :: Module
test = package "continuation" $ do
  contModuleDefs testContDef

testCont :: Coroutine_ ('[Uint16] :-> Uint8)
testCont ourCont = coroutine "testCont" $ CoroutineBody $ \escape -> do
  -- We must first get the exit continuation:
  exitCont <- escape

  comment "Following first yield"
  val <- indirect exitCont 0
  ifte_ (val >? 0)
    (comment "> 0")
    (comment "<= 0")
  comment "Following first indirect"
  exitCont2 <- escape
  comment "Following second yield"
  val2 <- indirect exitCont2 1

  retVoid

testContDef = coroutineDef_ testCont
