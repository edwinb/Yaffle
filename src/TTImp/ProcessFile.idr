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
import TTImp.ProcessData
import TTImp.ProcessDef
import TTImp.ProcessDirective
import TTImp.ProcessFailing
import TTImp.ProcessRecord
import TTImp.ProcessRunElab
import TTImp.ProcessTransform
import TTImp.ProcessType
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
  process eopts nest env (IClaim fc rig vis opts ty)
      = processType eopts nest env fc rig vis opts ty
  process eopts nest env (IData fc vis mbtot ddef)
      = processData eopts nest env fc vis mbtot ddef
  process eopts nest env (IDef fc fname def)
      = processDef eopts nest env fc fname def
--   process eopts nest env (IParameters fc ps decls)
--       = processParams nest env fc ps decls
  process eopts nest env (IRecord fc ns vis mbtot rec)
      = processRecord eopts nest env ns vis mbtot rec
  process eopts nest env (IFail fc msg decls)
      = processFailing eopts nest env fc msg decls
  process eopts nest env (INamespace fc ns decls)
      = withExtendedNS ns $
           traverse_ (processDecl eopts nest env) decls
  process eopts nest env (ITransform fc n lhs rhs)
      = processTransform eopts nest env fc n lhs rhs
--   process eopts nest env (IRunElabDecl fc tm)
--       = processRunElab eopts nest env fc tm
  process eopts nest env (IDirective fc d)
      = processDirective fc d
  process eopts nest env (IPragma _ _ act)
      = act nest env
  process eopts nest env (ILog lvl)
      = addLogLevel (uncurry unsafeMkLogLevel <$> lvl)
  process eopts nest env (IBuiltin fc type name)
      = processBuiltin nest env fc type name
  process eopts nest env y = ?remove_when_done

  export
  processDecls : {vars : _} ->
                 NestedNames vars -> Env Term vars -> List ImpDecl -> Core Bool
  processDecls nest env decls
      = do traverse_ (processDecl [] nest env) decls
           pure True -- TODO: False on error

  export
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

TTImp.Elab.Check.processDecl = process
