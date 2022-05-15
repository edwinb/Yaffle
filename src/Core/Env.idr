module Core.Env

import Core.TT
import Data.List

public export
data Env : (tm : List Name -> Type) -> List Name -> Type where
     Nil : Env tm []
     (::) : Binder (tm vars) -> Env tm vars -> Env tm (x :: vars)

%name Env env

export
length : Env tm xs -> Nat
length [] = 0
length (_ :: xs) = S (length xs)

export
lengthNoLet : Env tm xs -> Nat
lengthNoLet [] = 0
lengthNoLet (Let _ _ _ _ :: xs) = lengthNoLet xs
lengthNoLet (_ :: xs) = S (lengthNoLet xs)

revOnto : (xs, vs : _) -> reverseOnto xs vs = reverse vs ++ xs
revOnto xs [] = Refl
revOnto xs (v :: vs)
    = rewrite revOnto (v :: xs) vs in
        rewrite appendAssociative (reverse vs) [v] xs in
          rewrite revOnto [v] vs in Refl

revNs : (vs, ns : List a) -> reverse ns ++ reverse vs = reverse (vs ++ ns)
revNs [] ns = rewrite appendNilRightNeutral (reverse ns) in Refl
revNs (v :: vs) ns
    = rewrite revOnto [v] vs in
        rewrite revOnto [v] (vs ++ ns) in
          rewrite sym (revNs vs ns) in
            rewrite appendAssociative (reverse ns) (reverse vs) [v] in
              Refl

-- Weaken by all the names at once at the end, to save multiple traversals
-- in big environments
-- Also reversing the names at the end saves significant time over concatenating
-- when environments get fairly big.
getBinderUnder : Weaken tm =>
                 {vars : _} -> {idx : Nat} ->
                 (ns : List Name) ->
                 (0 p : IsVar x idx vars) -> Env tm vars ->
                 Binder (tm (reverseOnto vars ns))
getBinderUnder {idx = Z} {vars = v :: vs} ns First (b :: env)
    = rewrite revOnto vs (v :: ns) in map (weakenNs (reverse (mkSizeOf (v :: ns)))) b
getBinderUnder {idx = S k} {vars = v :: vs} ns (Later lp) (b :: env)
    = getBinderUnder (v :: ns) lp env

export
getBinder : Weaken tm =>
            {vars : _} -> {idx : Nat} ->
            (0 p : IsVar x idx vars) -> Env tm vars -> Binder (tm vars)
getBinder el env = getBinderUnder [] el env

public export
data IsDefined : Name -> List Name -> Type where
  MkIsDefined : {idx : Nat} -> RigCount -> (0 p : IsVar n idx vars) ->
                IsDefined n vars

export
defined : {vars : _} ->
          (n : Name) -> Env Term vars ->
          Maybe (IsDefined n vars)
defined n [] = Nothing
defined {vars = x :: xs} n (b :: env)
    = case nameEq n x of
           Nothing => do MkIsDefined rig prf <- defined n env
                         pure (MkIsDefined rig (Later prf))
           Just Refl => Just (MkIsDefined (multiplicity b) First)

-- Make a type which abstracts over an environment
-- Don't include 'let' bindings, since they have a concrete value and
-- shouldn't be generalised
export
abstractEnvType : {vars : _} ->
                  FC -> Env Term vars -> (tm : Term vars) -> Term []
abstractEnvType fc [] tm = tm
abstractEnvType fc (Let fc' c val ty :: env) tm
    = abstractEnvType fc env (Bind fc _ (Let fc' c val ty) tm)
abstractEnvType fc (Pi fc' c e ty :: env) tm
    = abstractEnvType fc env (Bind fc _ (Pi fc' c e ty) tm)
abstractEnvType fc (b :: env) tm
    = let bnd = Pi (binderLoc b) (multiplicity b) Explicit (binderType b)
       in abstractEnvType fc env (Bind fc _ bnd tm)

-- As above, for the corresponding term
export
abstractEnv : {vars : _} ->
              FC -> Env Term vars -> (tm : Term vars) -> Term []
abstractEnv fc [] tm = tm
abstractEnv fc (Let fc' c val ty :: env) tm
    = abstractEnv fc env (Bind fc _ (Let fc' c val ty) tm)
abstractEnv fc (b :: env) tm
    = let bnd = Lam (binderLoc b) (multiplicity b) Explicit (binderType b)
      in abstractEnv fc env (Bind fc _ bnd tm)

-- As above, but abstract over all binders including lets
export
abstractFullEnvType : {vars : _} ->
                      FC -> Env Term vars -> (tm : Term vars) -> Term []
abstractFullEnvType fc [] tm = tm
abstractFullEnvType fc (Pi fc' c e ty :: env) tm
    = abstractFullEnvType fc env (Bind fc _ (Pi fc' c e ty) tm)
abstractFullEnvType fc (b :: env) tm
    = let bnd = Pi fc (multiplicity b) Explicit (binderType b)
      in abstractFullEnvType fc env (Bind fc _ bnd tm)
