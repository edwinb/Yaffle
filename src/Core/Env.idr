module Core.Env

import Core.TT
import Data.List
import Data.SnocList

public export
data Env : (tm : SnocList Name -> Type) -> SnocList Name -> Type where
     Lin : Env tm [<]
     (:<) : Env tm vars -> Binder (tm vars) -> Env tm (vars :< x)

%name Env env

export
length : Env tm xs -> Nat
length [<] = 0
length (xs :< _) = S (length xs)

export
lengthNoLet : Env tm xs -> Nat
lengthNoLet [<] = 0
lengthNoLet (xs :< Let _ _ _ _) = lengthNoLet xs
lengthNoLet (xs :< _) = S (lengthNoLet xs)

-- Weaken by all the names at once at the end, to save multiple traversals
-- in big environments
-- Also reversing the names at the end saves significant time over concatenating
-- when environments get fairly big.
getBinderUnder : Weaken tm =>
                 {vars : _} -> {idx : Nat} ->
                 (ns : SnocList Name) ->
                 (0 p : IsVar x idx vars) -> Env tm vars ->
                 Binder (tm (reverseOnto vars ns))
getBinderUnder {idx = Z} {vars = vs :< v} ns First (env :< b)
    = rewrite revOnto (vs :< x) ns in
        rewrite sym $ appendAssociative vs [<v] (reverse ns) in
                map (weakenNs (sucR (reverse (mkSizeOf ns)))) b
getBinderUnder {idx = S k} {vars = vs :< v} ns (Later lp) (env :< b)
    = getBinderUnder (ns :< v) lp env

export
getBinder : Weaken tm =>
            {vars : _} -> {idx : Nat} ->
            (0 p : IsVar x idx vars) -> Env tm vars -> Binder (tm vars)
getBinder el env = getBinderUnder [<] el env

public export
data IsDefined : Name -> SnocList Name -> Type where
  MkIsDefined : {idx : Nat} -> RigCount -> (0 p : IsVar n idx vars) ->
                IsDefined n vars

export
defined : {vars : _} ->
          (n : Name) -> Env Term vars ->
          Maybe (IsDefined n vars)
defined n [<] = Nothing
defined {vars = xs :< x} n (env :< b)
    = case nameEq n x of
           Nothing => do MkIsDefined rig prf <- defined n env
                         pure (MkIsDefined rig (Later prf))
           Just Refl => Just (MkIsDefined (multiplicity b) First)

-- Bind additional pattern variables in an LHS, when checking an LHS in an
-- outer environment
export
bindEnv : {vars : _} -> FC -> Env Term vars -> (tm : Term vars) -> ClosedTerm
bindEnv loc [<] tm = tm
bindEnv loc (env :< b) tm
    = bindEnv loc env (Bind loc _ (PVar (binderLoc b)
                                        (multiplicity b)
                                        Explicit
                                        (binderType b)) tm)

-- Make a type which abstracts over an environment
-- Don't include 'let' bindings, since they have a concrete value and
-- shouldn't be generalised
export
abstractEnvType : {vars : _} ->
                  FC -> Env Term vars -> (tm : Term vars) -> Term [<]
abstractEnvType fc [<] tm = tm
abstractEnvType fc (env :< Let fc' c val ty) tm
    = abstractEnvType fc env (Bind fc _ (Let fc' c val ty) tm)
abstractEnvType fc (env :< Pi fc' c e ty) tm
    = abstractEnvType fc env (Bind fc _ (Pi fc' c e ty) tm)
abstractEnvType fc (env :< b) tm
    = let bnd = Pi (binderLoc b) (multiplicity b) Explicit (binderType b)
       in abstractEnvType fc env (Bind fc _ bnd tm)

-- As above, for the corresponding term
export
abstractEnv : {vars : _} ->
              FC -> Env Term vars -> (tm : Term vars) -> Term [<]
abstractEnv fc [<] tm = tm
abstractEnv fc (env :< Let fc' c val ty) tm
    = abstractEnv fc env (Bind fc _ (Let fc' c val ty) tm)
abstractEnv fc (env :< b) tm
    = let bnd = Lam (binderLoc b) (multiplicity b) Explicit (binderType b)
      in abstractEnv fc env (Bind fc _ bnd tm)

-- As above, but abstract over all binders including lets
export
abstractFullEnvType : {vars : _} ->
                      FC -> Env Term vars -> (tm : Term vars) -> Term [<]
abstractFullEnvType fc [<] tm = tm
abstractFullEnvType fc (env :< Pi fc' c e ty) tm
    = abstractFullEnvType fc env (Bind fc _ (Pi fc' c e ty) tm)
abstractFullEnvType fc (env :< b) tm
    = let bnd = Pi fc (multiplicity b) Explicit (binderType b)
      in abstractFullEnvType fc env (Bind fc _ bnd tm)

restrictWEnv : Env Term vars -> Env Term vars
restrictWEnv [<] = [<]
restrictWEnv (env :< b) = restrictWEnv env :< setMultiplicity b (rigRestrictW $ multiplicity b)

-- Restriction makes p-annotated variables that do not support at least q
-- copies unavailable at runtime
--
-- We use restriction to push the ambient quantity p onto the context:
--
--    X |- e :p A
-- =================
-- X \ p |- e :|p| A
--
-- where |p| is `presence p`
--
-- Note: when p is Rig0, all context quantities are ignored.
export
restrictEnv : Env Term vars -> RigCount -> Env Term vars
restrictEnv env RigW = restrictWEnv env
restrictEnv env _ = env

export
mkEnvOnto : FC -> (xs : SnocList Name) -> Env Term ys -> Env Term (ys ++ xs)
mkEnvOnto fc [<] vs = vs
mkEnvOnto fc (ns :< n) vs
   = mkEnvOnto fc ns vs :< PVar fc top Explicit (Erased fc Placeholder)

-- Make a dummy environment, if we genuinely don't care about the values
-- and types of the contents.
-- We use this when building and comparing case trees.
export
mkEnv : FC -> (vs : SnocList Name) -> Env Term vs
mkEnv fc [<] = [<]
mkEnv fc (ns :< n) = mkEnv fc ns :< PVar fc top Explicit (Erased fc Placeholder)
