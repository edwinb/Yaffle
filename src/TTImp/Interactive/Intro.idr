module TTImp.Interactive.Intro

import Core.Core
import Core.Context
import Core.Env
import Core.Evaluate
import Core.Metadata
import Core.TT
import Core.Unify

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.TTImp
import TTImp.Unelab
import TTImp.Utils

%default covering

parameters
  {lhsCtxt : _ }
  {auto c : Ref Ctxt Defs}
  {auto m : Ref MD Metadata}
  {auto u : Ref UST UState}
  (hidx : Int)
  (hole : Name)
  (env : Env Term lhsCtxt)

  introLam : Name -> RigCount -> Term lhsCtxt -> Core IRawImp
  introLam x rig ty = do
    ty <- unelab env ty
    defs <- get Ctxt
    new_hole <- uniqueHoleName [] (nameRoot hole)
    let iintrod = ILam replFC rig Explicit (Just x) ty (IHole replFC new_hole)
    pure iintrod

  countPis : Term vars -> Nat
  countPis (Bind _ _ (Pi{}) sc) = S (countPis sc)
  countPis _ = Z

  introCon : Name -> Term lhsCtxt -> Core (List IRawImp)
  introCon n ty = do
    defs <- get Ctxt
    ust <- get UST
    Just gdef <- lookupCtxtExact n (gamma defs)
      | _ => pure []
    -- for now we only handle types with a unique constructor
    let TCon ti _ = definition gdef
      | _ => pure []
    gty <- nf env ty
    let cs = datacons ti
    ics <- for cs $ \ cons => do
      Just gdef <- lookupCtxtExact cons (gamma defs)
        | _ => pure Nothing
      let nargs = countPis (type gdef)
      new_hole_names <- uniqueHoleNames nargs (nameRoot hole)
      let new_holes = IHole replFC <$> new_hole_names
      let icons = apply (IVar replFC cons) new_holes
      res <- catch
        (do -- We're desugaring it to the corresponding TTImp
            ccons <- checkTerm hidx {-is this correct?-} InExpr [] (MkNested []) env icons gty
            ncons <- normaliseHoles env ccons
            icons <- unelab env ncons
            pure (Just icons))
        (\ _ => pure Nothing)
      put Ctxt defs -- reset the context, we don't want any updates
      put UST ust
      pure res
    pure (catMaybes ics)

  export
  intro : Term lhsCtxt -> Core (List IRawImp)
  -- structural cases
  intro (Bind _ x (Let _ _ ty val) sc) = toList <$> intro (subst val sc)
  intro (TDelayed _ _ t) = intro t
  -- interesting ones
  intro (Bind _ x (Pi _ rig Explicit ty) _) = pure <$> introLam x rig ty
  intro t = case getFnArgs t of
    (Ref _ (TyCon ar) n, _) => introCon n t
    _ => pure []
