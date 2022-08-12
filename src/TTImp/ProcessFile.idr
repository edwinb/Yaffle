module TTImp.ProcessFile

import Core.Context
import Core.Directory
import Core.Error
import Core.InitPrimitives
import Core.Unify.State

import Parser.Source
import TTImp.Parser
import TTImp.TTImp

import System
import System.File

parameters {auto c : Ref Ctxt Defs}
  processTTImpFile : String -> Core Bool
  processTTImpFile fname
      = do modIdent <- ctxtPathToNS fname
           Right (ws, decor, tti) <-
                coreLift $ parseFile fname (PhysicalIdrSrc modIdent)
                              (do decls <- prog (PhysicalIdrSrc modIdent)
                                  eoi
                                  pure decls)
                 | Left err => do coreLift (putStrLn (show err))
                                  pure False
           traverse_ recordWarning ws

           throw (InternalError "Elaboration not done yet")

export
ttImpMain : String -> Core ()
ttImpMain fname
    = do defs <- initDefs
         c <- newRef Ctxt defs
         addPrimitives
         ok <- processTTImpFile fname
         -- TODO: when ok, write out TTC
         pure ()
