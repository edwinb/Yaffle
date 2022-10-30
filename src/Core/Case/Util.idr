module Core.Case.Util

import Core.TT
import Core.Context
import Core.Evaluate

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

emptyRHS : FC -> Term vars -> Term vars
emptyRHS fc (Case cfc c sc scTy alts) = Case cfc c sc scTy (map emptyRHSalt alts)
  where
    emptyRHSscope : forall vars . FC -> CaseScope vars -> CaseScope vars
    emptyRHSscope fc (RHS tm) = RHS (emptyRHS fc tm)
    emptyRHSscope fc (Arg c x sc) = Arg c x (emptyRHSscope fc sc)

    emptyRHSalt : forall vars . CaseAlt vars -> CaseAlt vars
    emptyRHSalt (ConCase fc n t sc) = ConCase fc n t (emptyRHSscope fc sc)
    emptyRHSalt (DelayCase fc c arg sc) = DelayCase fc c arg (emptyRHS fc sc)
    emptyRHSalt (ConstCase fc c sc) = ConstCase fc c (emptyRHS fc sc)
    emptyRHSalt (DefaultCase fc sc) = DefaultCase fc (emptyRHS fc sc)
emptyRHS fc _ = Erased fc Placeholder

export
mkAlt : {vars : _} ->
        FC -> Term vars -> DataCon -> CaseAlt vars
mkAlt fc sc (MkDataCon cn t ar qs)
    = ConCase fc cn t (mkScope qs (map (MN "m") (take ar [0..])))
  where
    mkScope : List RigCount -> SnocList Name -> CaseScope vars
    mkScope _ [<] = RHS (emptyRHS fc sc)
    mkScope [] (vs :< v) = Arg top v (weaken (mkScope [] vs))
    mkScope (q :: qs) (vs :< v) = Arg q v (weaken (mkScope qs vs))

export
tagIs : Int -> CaseAlt vars -> Bool
tagIs t (ConCase _ _ t' _) = t == t'
tagIs t (ConstCase{}) = False
tagIs t (DelayCase{}) = False
tagIs t (DefaultCase{}) = True
