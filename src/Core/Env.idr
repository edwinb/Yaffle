module Core.Env

import Core.TT
import Data.List
import Data.SnocList
import Data.Vect

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

getLetUnder : Weaken tm =>
                 {vars : _} -> {idx : Nat} ->
                 (ns : SnocList Name) ->
                 (0 p : IsVar x idx vars) -> Env tm vars ->
                 Maybe (tm (reverseOnto vars ns))
getLetUnder {idx = Z} {vars = vs :< v} ns First (env :< Let _ _ val _)
    = rewrite revOnto (vs :< x) ns in
        rewrite sym $ appendAssociative vs [<v] (reverse ns) in
                Just $ weakenNs (sucR (reverse (mkSizeOf ns))) val
getLetUnder {idx = S k} {vars = vs :< v} ns (Later lp) (env :< b)
    = getLetUnder (ns :< v) lp env
getLetUnder _ _ _ = Nothing

-- as getBinder but only return result if it's a let bound name
-- to save unnecessary weakening
export
getLet : Weaken tm =>
         {vars : _} -> {idx : Nat} ->
         (0 p : IsVar x idx vars) -> Env tm vars -> Maybe (tm vars)
getLet el env = getLetUnder [<] el env

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

export
letToLam : Env Term vars -> Env Term vars
letToLam [<] = [<]
letToLam (env :< Let fc c val ty) = letToLam env :< Lam fc c Explicit ty
letToLam (env :< b) = letToLam env :< b

mutual
  dropS : SnocList Nat -> SnocList Nat
  dropS [<] = [<]
  dropS (xs :< Z) = dropS xs
  dropS (xs :< S p) = dropS xs :< p

  -- Quicker, if less safe, to store variables as a Nat, for quick comparison
  findUsed : {vars : _} ->
             Env Term vars -> SnocList Nat -> Term vars -> SnocList Nat
  findUsed env used (Local fc idx p)
      = if elemBy eqNat idx used
           then used
           else assert_total (findUsedInBinder env (used :< idx)
                                               (getBinder p env))
    where
      eqNat : Nat -> Nat -> Bool
      eqNat i j = natToInteger i == natToInteger j
  findUsed env used (Meta _ _ _ args)
      = findUsedArgs env used (map snd args)
    where
      findUsedArgs : Env Term vars -> SnocList Nat -> List (Term vars) -> SnocList Nat
      findUsedArgs env u [] = u
      findUsedArgs env u (a :: as)
          = findUsedArgs env (findUsed env u a) as
  findUsed env used (Bind fc x b tm)
      = assert_total $
          dropS (findUsed (env :< b)
                          (map S (findUsedInBinder env used b))
                          tm)
  findUsed env used (App fc fn c arg)
      = findUsed env (findUsed env used fn) arg
  findUsed env used (As fc s a p)
      = findUsed env used p
  findUsed env used (Case fc c sc scTy alts)
      = findUsedAlts env (findUsed env (findUsed env used sc) scTy) alts
    where
      findUsedScope : {vars : _} ->
                      FC -> Env Term vars -> SnocList Nat -> CaseScope vars ->
                      SnocList Nat
      findUsedScope fc env used (RHS tm) = findUsed env used tm
      findUsedScope fc env used (Arg c x sc)
         = assert_total $
              dropS (findUsedScope fc
                       (env :< PVar fc top Explicit (Erased fc Placeholder))
                       used sc)

      findUsedAlt : {vars : _} ->
                    Env Term vars -> SnocList Nat -> CaseAlt vars ->
                    SnocList Nat
      findUsedAlt env used (ConCase fc n t sc) = findUsedScope fc env used sc
      findUsedAlt env used (DelayCase fc t a tm)
          = findUsed (env :< PVar fc top Explicit (Erased fc Placeholder)
                          :< PVar fc top Explicit (Erased fc Placeholder))
                     used tm
      findUsedAlt env used (ConstCase fc c tm) = findUsed env used tm
      findUsedAlt env used (DefaultCase fc tm) = findUsed env used tm

      findUsedAlts : {vars : _} ->
                     Env Term vars -> SnocList Nat -> List (CaseAlt vars) ->
                     SnocList Nat
      findUsedAlts env used [] = used
      findUsedAlts env used (a :: as)
          = findUsedAlts env (findUsedAlt env used a) as
  findUsed env used (TDelayed fc r tm)
      = findUsed env used tm
  findUsed env used (TDelay fc r ty tm)
      = findUsed env (findUsed env used ty) tm
  findUsed env used (TForce fc r tm)
      = findUsed env used tm
  findUsed env used (PrimOp fc f args)
      = findUsedArgs env used args
    where
      findUsedArgs : Env Term vars -> SnocList Nat -> Vect arity (Term vars) -> SnocList Nat
      findUsedArgs env u [] = u
      findUsedArgs env u (a :: as)
          = findUsedArgs env (findUsed env u a) as
  findUsed env used _ = used

  findUsedInBinder : {vars : _} ->
                     Env Term vars -> SnocList Nat ->
                     Binder (Term vars) -> SnocList Nat
  findUsedInBinder env used (Let _ _ val ty)
    = findUsed env (findUsed env used val) ty
  findUsedInBinder env used (PLet _ _ val ty)
    = findUsed env (findUsed env used val) ty
  findUsedInBinder env used b = findUsed env used (binderType b)

toVar : (vars : SnocList Name) -> Nat -> Maybe (Var vars)
toVar (vs :< v) Z = Just (MkVar First)
toVar (vs :< v) (S k)
   = do MkVar prf <- toVar vs k
        Just (MkVar (Later prf))
toVar _ _ = Nothing

export
findUsedLocs : {vars : _} ->
               Env Term vars -> Term vars -> SnocList (Var vars)
findUsedLocs env tm
    = mapMaybe (toVar _) (findUsed env [<] tm)

isUsed : Nat -> SnocList (Var vars) -> Bool
isUsed n [<] = False
isUsed n (vs :< v) = n == varIdx v || isUsed n vs

mkShrinkSub : {n : _} ->
              (vars : _) -> SnocList (Var (vars :< n)) ->
              (newvars ** SubVars newvars (vars :< n))
mkShrinkSub [<] els
    = if isUsed 0 els
         then (_ ** KeepCons SubRefl)
         else (_ ** DropCons SubRefl)
mkShrinkSub (xs :< x) els
    = let (_ ** subRest) = mkShrinkSub xs (dropFirst els) in
      if isUsed 0 els
        then (_ ** KeepCons subRest)
        else (_ ** DropCons subRest)

mkShrink : {vars : _} ->
           SnocList (Var vars) ->
           (newvars ** SubVars newvars vars)
mkShrink {vars = [<]} xs = (_ ** SubRefl)
mkShrink {vars = vs :< v} xs = mkShrinkSub _ xs

-- Find the smallest subset of the environment which is needed to type check
-- the given term
export
findSubEnv : {vars : _} ->
             Env Term vars -> Term vars ->
             (vars' : SnocList Name ** SubVars vars' vars)
findSubEnv env tm = mkShrink (findUsedLocs env tm)

export
shrinkEnv : Env Term vars -> SubVars newvars vars -> Maybe (Env Term newvars)
shrinkEnv env SubRefl = Just env
shrinkEnv (env :< b) (DropCons p) = shrinkEnv env p
shrinkEnv (env :< b) (KeepCons p)
    = do env' <- shrinkEnv env p
         b' <- assert_total (shrinkBinder b p)
         pure (env' :< b')

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

export
allVars : {vars : _} -> Env Term vars -> List (Var vars)
allVars [<] = []
allVars (vs :< v) = MkVar First :: map weaken (allVars vs)

export
allVarsNoLet : {vars : _} -> Env Term vars -> List (Var vars)
allVarsNoLet [<] = []
allVarsNoLet (vs :< Let _ _ _ _) = map weaken (allVars vs)
allVarsNoLet (vs :< v) = MkVar First :: map weaken (allVars vs)
