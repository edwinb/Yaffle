module TTImp.ProcessFile

import Core.Context
import Core.Directory
import Core.Error
import Core.InitPrimitives
import Core.Metadata
import Core.Unify.State

import Parser.Source
import TTImp.Parser
import TTImp.TTImp

import System
import System.File

parameters {auto c : Ref Ctxt Defs} {auto u : Ref UST UState}
           {auto m : Ref MD Metadata}
  processTTImpDecls : NestedNames vars -> Env Term vars ->
                      List ImpDecl -> Core Bool

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
           m <- newRef MD (initMetadata (PhysicalIdrSrc modIdent))
           u <- newRef UST initUState

           catch (do ignore $ processTTImpDecls (MkNested []) [<] tti
                     Nothing <- checkDelayedHoles
                         | Just err => throw err
                     pure True)
                 (\err => do coreLift_ (printLn err)
                             pure False)

export
ttImpMain : String -> Core ()
ttImpMain fname
    = do defs <- initDefs
         c <- newRef Ctxt defs
         addPrimitives
         ok <- processTTImpFile fname
         -- TODO: when ok, write out TTC
         pure ()
