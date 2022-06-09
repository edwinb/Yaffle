module Core.Check.Linear

-- Linearity checking of already typechecked/elaborated terms
-- Assumption: Terms are already type correct and we're only checking usage.
-- of local variables.
-- We must be able to complete linearity checking without reference to the
-- global context, although we are allowed to accuess the global context to
-- update quantities in hold types.

import Core.Env
import Core.Error
import Core.TT

-- List of variable usages - we'll count the contents of specific variables
-- when discharging binders, to ensure that linear names are only used once
data Usage : SnocList Name -> Type where
     Lin : Usage vars
     (:<) : Usage vars -> Var vars -> Usage vars

Show (Usage vars) where
  show xs = "[" ++ showAll xs ++ "]"
    where
      showAll : Usage vs -> String
      showAll [<] = ""
      showAll [<el] = show el
      showAll (xs :< x) = show xs ++ ", " ++ show x

doneScope : Usage (vars :< n) -> Usage vars
doneScope [<] = [<]
doneScope (xs :< MkVar First) = doneScope xs
doneScope (xs :< MkVar (Later p)) = doneScope xs :< MkVar p

(++) : Usage ns -> Usage ns -> Usage ns
(++) ys [<] = ys
(++) ys (x :< xs) = ys ++ x :< xs

count : Nat -> Usage ns -> Nat
count p [<] = 0
count p (xs :< v)
    = if p == varIdx v then 1 + count p xs else count p xs

parameters {auto c : Ref Ctxt Defs}

  updateHoleUsage : {vars : _} ->
                    Var vars -> List (Var vars) ->
                    Term vars -> Core Bool

  lcheck : {vars : _} ->
           RigCount -> Env Term vars -> Term vars -> Core (Usage vars)

  -- Checking if the bound variable is used appropriately in the scope
  checkUsageOK : FC -> Nat -> Name -> RigCount -> Core ()
  checkUsageOK fc used nm r
      = when (isLinear r && used /= 1)
          (throw (LinearUsed fc used nm))

  lcheckAlt : {vars : _} ->
              (scrig : RigCount) ->
              (rhsrig : RigCount) ->
              Env Term vars -> CaseAlt vars ->
              Core (Usage vars)
  lcheckAlt scrig rig env (ConCase fc n t sc) = ?foo1
  lcheckAlt scrig rig env (DelayCase fc t a rhs)
      = do -- t and a are RigW, so just add them to the environment as scrig
           let env'
               = env :<
                 PVar fc scrig Implicit (TType fc (MN "top" 0)) :<
                 PVar fc scrig Explicit (Local fc Nothing _ First)
           u' <- lcheck rig env' rhs
           let usedt = count 1 u'
           let useda = count 0 u'
           checkUsageOK EmptyFC usedt t (rigMult scrig rig)
           checkUsageOK EmptyFC useda a (rigMult scrig rig)
           pure (doneScope (doneScope u'))
  lcheckAlt scrig rig env (ConstCase fc c rhs) = lcheck rig env rhs
  lcheckAlt scrig rig env (DefaultCase fc rhs) = lcheck rig env rhs

  lcheckAlts : {vars : _} ->
               (scrig : RigCount) ->
               (rhsrig : RigCount) ->
               Env Term vars -> List (CaseAlt vars) ->
               Core (Usage vars)
  lcheckAlts scrig rig env [] = pure [<]
  lcheckAlts scrig rig env (a :: alts)
     = do ua <- lcheckAlt scrig rig env a
          ualts <- lcheckAlts scrig rig env alts
          pure (ua ++ ualts)

  lcheckBinder : {vars : _} ->
           RigCount -> Env Term vars -> Binder (Term vars) -> Core (Usage vars)

  lcheck {vars} rig env (Local fc x idx prf)
      = let b = getBinder prf env
            rigb = multiplicity b in
            do rigSafe rigb rig
               pure (used rig)
    where
      getName : {idx : _} -> (vs : SnocList Name) -> (0 p : IsVar n idx vs) -> Name
      getName (_ :< x) First = x
      getName (xs :< x) (Later p) = getName xs p

      rigSafe : RigCount -> RigCount -> Core ()
      rigSafe l r = when (l < r)
                         (throw (LinearMisuse fc (getName vars prf) l r))

      -- count the usage if we're in a linear context. If not, the usage doesn't
      -- matter
      used : RigCount -> Usage vars
      used r = if isLinear r then [<MkVar prf] else [<]
  lcheck rig env (Ref fc nt n)
      = pure [<] -- No quantity to check, and the name's quantity was checked
                 -- when type checking
  lcheck rig env (Meta fc n i args) = ?todoMeta
  lcheck rig_in env (Bind fc nm b sc)
      = do ub <- lcheckBinder rig env b
           usc <- lcheck rig (env :< b) sc
           let used = count 0 usc
           -- TODO holes in the scope

           checkUsageOK fc used nm (rigMult (multiplicity b) rig)
           pure (ub ++ doneScope usc)
    where
      rig : RigCount
      rig = case b of
                 Pi _ _ _ _ =>
                      if isErased rig_in
                         then erased
                         else top -- checking as if an inspectable run-time type
                 Let _ _ _ _ => rig_in
                 _ => if isErased rig_in
                         then erased
                         else linear -- checking as if top level function declaration

  lcheck rig env (App fc fn q arg)
      = do uf <- lcheck rig env fn
           ua <- lcheck (rigMult rig q) env arg
           pure (uf ++ ua)
  lcheck rig env (As fc s var pat)
      = lcheck rig env pat
  lcheck rig env (Case fc scrig sc ty alts)
      = do usc <- lcheck rig env sc
           ualts <- lcheckAlts scrig rig env alts
           pure (usc ++ ualts)
  lcheck _ _ _ = ?todo

  checkEnvUsage : {vars, done : _} ->
                  FC -> RigCount ->
                  Env Term vars -> Usage (vars ++ done) ->
                  Term (vars ++ done) ->
                  Core ()

  export
  linearCheck : {vars : _} ->
                FC -> RigCount -> Env Term vars -> Term vars -> Core ()
  linearCheck fc rig env tm
      = do used <- lcheck rig env tm
           checkEnvUsage {done = [<]} fc rig env used tm
