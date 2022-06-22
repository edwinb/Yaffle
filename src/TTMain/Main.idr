-- Top level app for a typechecker for the Raw TT syntax
-- plus
module TTMain.Main

import Core.Context
import Core.Error
import Core.InitPrimitives
import Core.Syntax.Parser
import Core.Syntax.Raw
import Core.Unify.State

import TTMain.ProcessTT
import TTMain.REPL

import System
import System.File

ttMain : String -> Core ()
ttMain fname
    = do Right inp <- coreLift $ readFile fname
             | Left err => throw (FileErr (SystemFileErr fname err))
         let origin = PhysicalIdrSrc $ nsAsModuleIdent (unsafeFoldNamespace ["Main"])
         let Right cmds = parse origin (rawInput origin) inp
             | Left err => throw err
         -- Initialise context with primitive ops
         defs <- initDefs
         c <- newRef Ctxt defs
         u <- newRef UST initUState
         addPrimitives
         -- And we're off. Process the commands from the input file...
         catch (traverse_ processCommand cmds)
               (\err => throw !(toFullNames err))
         -- ...and start the REPL
         repl

usage : String
usage = "Usage: yaffle <input file>"

main : IO ()
main
    = do (_ :: fname :: []) <- getArgs
             | _ => do putStrLn usage
                       exitWith (ExitFailure 1)
         coreRun (ttMain fname)
               (\err : Error => putStrLn ("Uncaught error: " ++ show err))
               (\res => pure ())

