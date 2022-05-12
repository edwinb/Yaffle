module TTMain.REPL

import Core.Context
import Core.Error
import Core.Syntax.Parser
import Core.Syntax.Raw

import TTMain.ProcessTT

import System.File

parameters {auto c: Ref Ctxt Defs}

  -- All the REPL does is
  export
  repl : Core ()
  repl
      = do coreLift_ $ putStr "Yaffle> "
           coreLift_ (fflush stdout)
           inp <- coreLift getLine
           end <- coreLift $ fEOF stdin
           if end
             then coreLift_ $ putStrLn "Bye for now!"
             else do let origin = Virtual Interactive
                     let Right cmd = parse origin (command origin) (inp ++ ";")
                             | Left err =>
                                   do coreLift_ $ putStrLn (show err)
                                      repl
                     case cmd of
                          Quit => coreLift_ $ putStrLn "Bye for now!"
                          _ => do processCommand cmd
                                  repl


