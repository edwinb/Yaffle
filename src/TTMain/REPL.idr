module TTMain.REPL

import Core.Context
import Core.Context.Log
import Core.Error
import Core.Syntax.Parser
import Core.Syntax.Raw
import Core.Unify.State

import TTMain.ProcessTT

import System.File

parameters {auto c: Ref Ctxt Defs} {auto u : Ref UST UState}

  -- All the REPL does is read and process commands as defined in Decls,
  -- same as the commands in input files
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
                          _ => do logTimeWhen True "" $ processCommand cmd
                                  repl
