module TTImp.ProcessFile

import Core.Context
import Core.Directory
import Core.Error
import Core.InitPrimitives
import Core.Metadata
import Core.Unify.State

import Parser.Source
import TTImp.BindImplicits
import TTImp.Parser
import TTImp.ProcessBuiltin
import TTImp.TTImp
import TTImp.Elab.Check

import System
import System.File

import Data.SnocList

parameters {auto c : Ref Ctxt Defs}
           {auto m : Ref MD Metadata}
           {auto u : Ref UST UState}

  -- Implements processDecl, declared in TTImp.Elab.Check
  process : {vars : _} ->
            List ElabOpt ->
            NestedNames vars -> Env Term vars -> ImpDecl -> Core ()

  export
  processDecls : {vars : _} ->
                 NestedNames vars -> Env Term vars -> List ImpDecl -> Core Bool
  processDecls nest env decls
      = do traverse_ (processDecl [] nest env) decls
           pure True -- TODO: False on error

  processTTImpDecls : {vars : _} ->
                      NestedNames vars -> Env Term vars ->
                      List ImpDecl -> Core Bool
  processTTImpDecls {vars} nest env decls
      = do traverse_ (\d => do d' <- bindNames d
                               processDecl [] nest env d') decls
           pure True -- TODO: False on error
    where
      bindConNames : ImpTy -> Core ImpTy
      bindConNames (MkImpTy fc nameFC n ty)
          = do ty' <- bindTypeNames fc [] (cast vars) ty
               pure (MkImpTy fc nameFC n ty')

      bindDataNames : ImpData -> Core ImpData
      bindDataNames (MkImpData fc n t opts cons)
          = do t' <- bindTypeNames fc [] (cast vars) t
               cons' <- traverse bindConNames cons
               pure (MkImpData fc n t' opts cons')
      bindDataNames (MkImpLater fc n t)
          = do t' <- bindTypeNames fc [] (cast vars) t
               pure (MkImpLater fc n t')

      -- bind implicits to make raw TTImp source a bit friendlier
      bindNames : ImpDecl -> Core ImpDecl
      bindNames (IClaim fc c vis opts (MkImpTy tfc nameFC n ty))
          = do ty' <- bindTypeNames fc [] (cast vars) ty
               pure (IClaim fc c vis opts (MkImpTy tfc nameFC n ty'))
      bindNames (IData fc vis mbtot d)
          = do d' <- bindDataNames d
               pure (IData fc vis mbtot d')
      bindNames d = pure d

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

TTImp.Elab.Check.processDecl = process

export
ttImpMain : String -> Core ()
ttImpMain fname
    = do defs <- initDefs
         c <- newRef Ctxt defs
         addPrimitives
         ok <- processTTImpFile fname
         -- TODO: when ok, write out TTC
         pure ()
