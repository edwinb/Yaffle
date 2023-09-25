module TTImp.Elab.Dot

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Metadata
import Core.Evaluate
import Core.Unify
import Core.TT

import TTImp.Elab.Check
import TTImp.TTImp

%default covering

export
registerDot : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto e : Ref EST (EState vars)} ->
              RigCount -> Env Term vars ->
              FC -> DotReason ->
              Term vars -> Glued vars ->
              Core (Term vars, Glued vars)
registerDot rig env fc reason wantedTm gexpty
    = do nm <- genName "dotTm"
         expty <- quote env gexpty
         metaval <- metaVar fc rig env nm expty
         addDot fc env nm wantedTm reason metaval
         logTerm "unify.constraint" 5 "Register dot" wantedTm
         let tm = case reason of
                    UserDotted => Erased fc (Dotted metaval)
                    _ => metaval
         pure (tm, gexpty)

export
checkDot : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           RigCount -> ElabInfo ->
           NestedNames vars -> Env Term vars ->
           FC -> DotReason -> RawImp -> Maybe (Glued vars) ->
           Core (Term vars, Glued vars)
checkDot rig elabinfo nest env fc reason tm Nothing
    = throw (GenericMsg fc ("Dot pattern not valid here (unknown type) "
                            ++ show tm))
checkDot rig elabinfo nest env fc reason tm (Just gexpty)
    = case elabMode elabinfo of
        InLHS _ =>
          do (wantedTm, wantedTy) <- check rig
                                              ({ elabMode := InExpr }
                                                  elabinfo)
                                              nest env
                                              tm (Just gexpty)
             registerDot rig env fc reason wantedTm gexpty
        _ => throw (GenericMsg fc ("Dot pattern not valid here (Not LHS) "
                                   ++ show tm))
