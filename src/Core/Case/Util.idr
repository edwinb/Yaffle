module Core.Case.Util

import Core.Case.Tree
import Core.Context
import Core.Evaluate
import Core.TT

import Data.SnocList

public export
record DataCon where
  constructor MkDataCon
  name  : Name
  tag   : Int
  arity : Nat
  quantities : List RigCount

||| Given a normalised type, get all the possible constructors for that
||| type family, with their type, name, tag, and arity.
export
getCons : {auto c : Ref Ctxt Defs} ->
          {vars : _} ->
          Defs -> NF vars -> Core (List DataCon)
getCons defs (VTCon _ tn _ _)
    = case !(lookupDefExact tn (gamma defs)) of
           Just (TCon ti _) =>
                do cs' <- traverse addTy (datacons ti)
                   pure (catMaybes cs')
           _ => throw (InternalError "Called `getCons` on something that is not a Type constructor")
  where
    addTy : Name -> Core (Maybe DataCon)
    addTy cn
        = do Just gdef <- lookupCtxtExact cn (gamma defs)
                  | _ => pure Nothing
             case (gdef.definition, gdef.type) of
                  (DCon di t arity, ty) =>
                        pure . Just $ MkDataCon cn t arity (quantities di)
                  _ => pure Nothing
getCons defs _ = pure []

emptyRHS : FC -> CaseTree vars -> CaseTree vars
emptyRHS fc (TCase cfc c idx p scTy alts)
    = TCase cfc c idx p scTy (map emptyRHSalt alts)
  where
    emptyRHSscope : forall vars . FC -> TCaseScope vars -> TCaseScope vars
    emptyRHSscope fc (TRHS tm) = TRHS (emptyRHS fc tm)
    emptyRHSscope fc (TArg c x sc) = TArg c x (emptyRHSscope fc sc)

    emptyRHSalt : forall vars . TCaseAlt vars -> TCaseAlt vars
    emptyRHSalt (TConCase fc n t sc) = TConCase fc n t (emptyRHSscope fc sc)
    emptyRHSalt (TDelayCase fc c arg sc) = TDelayCase fc c arg (emptyRHS fc sc)
    emptyRHSalt (TConstCase fc c sc) = TConstCase fc c (emptyRHS fc sc)
    emptyRHSalt (TDefaultCase fc sc) = TDefaultCase fc (emptyRHS fc sc)
emptyRHS fc (STerm i s) = STerm i (Erased fc Placeholder)
emptyRHS fc sc = sc

export
mkAlt : {vars : _} ->
        FC -> CaseTree vars -> DataCon -> TCaseAlt vars
mkAlt fc sc (MkDataCon cn t ar qs)
    = TConCase fc cn t (mkScope qs (map (MN "m") (take ar [0..])))
  where
    mkScope : List RigCount -> SnocList Name -> TCaseScope vars
    mkScope _ [<] = TRHS (emptyRHS fc sc)
    mkScope [] (vs :< v) = TArg top v (weaken (mkScope [] vs))
    mkScope (q :: qs) (vs :< v) = TArg q v (weaken (mkScope qs vs))

emptyRHSTm : FC -> Term vars -> Term vars
emptyRHSTm fc (Case cfc c sc scTy alts) = Case cfc c sc scTy (map emptyRHSalt alts)
  where
    emptyRHSscope : forall vars . FC -> CaseScope vars -> CaseScope vars
    emptyRHSscope fc (RHS tm) = RHS (emptyRHSTm fc tm)
    emptyRHSscope fc (Arg c x sc) = Arg c x (emptyRHSscope fc sc)

    emptyRHSalt : forall vars . CaseAlt vars -> CaseAlt vars
    emptyRHSalt (ConCase fc n t sc) = ConCase fc n t (emptyRHSscope fc sc)
    emptyRHSalt (DelayCase fc c arg sc) = DelayCase fc c arg (emptyRHSTm fc sc)
    emptyRHSalt (ConstCase fc c sc) = ConstCase fc c (emptyRHSTm fc sc)
    emptyRHSalt (DefaultCase fc sc) = DefaultCase fc (emptyRHSTm fc sc)
emptyRHSTm fc tm@(Unmatched _ _) = tm
emptyRHSTm fc _ = Erased fc Placeholder

export
mkAltTm : {vars : _} ->
        FC -> Term vars -> DataCon -> CaseAlt vars
mkAltTm fc sc (MkDataCon cn t ar qs)
    = ConCase fc cn t (mkScope qs (map (MN "m") (take ar [0..])))
  where
    mkScope : List RigCount -> SnocList Name -> CaseScope vars
    mkScope _ [<] = RHS (emptyRHSTm fc sc)
    mkScope [] (vs :< v) = Arg top v (weaken (mkScope [] vs))
    mkScope (q :: qs) (vs :< v) = Arg q v (weaken (mkScope qs vs))

export
tagIs : Int -> TCaseAlt vars -> Bool
tagIs t (TConCase _ _ t' _) = t == t'
tagIs t (TConstCase{}) = False
tagIs t (TDelayCase{}) = False
tagIs t (TDefaultCase{}) = True

export
tagIsTm : Int -> CaseAlt vars -> Bool
tagIsTm t (ConCase _ _ t' _) = t == t'
tagIsTm t (ConstCase{}) = False
tagIsTm t (DelayCase{}) = False
tagIsTm t (DefaultCase{}) = True
