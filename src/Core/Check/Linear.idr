module Core.Check.Linear

-- Linearity checking of already typechecked/elaborated terms
-- Assumption: Terms are already type correct and we're only checking usage.
-- of local variables.
-- We must be able to complete linearity checking without reference to the
-- global context, although we are allowed to accuess the global context to
-- update quantities in hold types.

import Core.Context
import Core.Context.Log
import Core.Env
import Core.Error
import Core.TT

import Data.SnocList
import Data.Vect

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
(++) ys (xs :< x) = (ys ++ xs) :< x

concat : List (Usage ns) -> Usage ns
concat [] = [<]
concat (u :: us) = u ++ concat us

count : Nat -> Usage ns -> Nat
count p [<] = 0
count p (xs :< v)
    = if p == varIdx v then 1 + count p xs else count p xs

localPrf : {later : _} -> Var (vars :< n ++ later)
localPrf {later = [<]} = MkVar First
localPrf {n} {vars} {later = (xs :< x)}
    = let MkVar p = localPrf {n} {vars} {later = xs} in
          MkVar (Later p)

parameters {auto c : Ref Ctxt Defs}

  -- Look for holes in the scope. On finding one, update its type so that
  -- the variable in question's usage is set appropriately. If 'useVar' is
  -- set, then leave its multiplicity alone, otherwise set its multiplicity
  -- to zero.
  -- This is so that, in interactive editing, a user can see whether a variable
  -- is available for usage in a hole or not.
  updateHoleUsage : {vars : _} ->
                    (useVar : Bool) -> -- Should the variable be used in the scope?
                    Var vars -> -- Variable in question
                    List (Var vars) -> -- Variables with multiplicity 0
                    Term vars -> Core Bool

  -- ...and its mutually defined helpers
  updateHoleUsageArgs : {vars : _} ->
                    (useVar : Bool) ->
                    Var vars ->
                    List (Var vars) ->
                    List (Term vars) -> Core Bool
  updateHoleUsageArgs useVar var zs [] = pure False
  updateHoleUsageArgs useVar var zs (a :: as)
      = do h <- updateHoleUsage useVar var zs a
           h' <- updateHoleUsageArgs useVar var zs as
           pure (h || h')

  updateHoleUsageScope : {vars : _} ->
                    (useVar : Bool) ->
                    Var vars ->
                    List (Var vars) ->
                    CaseScope vars -> Core Bool
  updateHoleUsageScope useVar var zs (RHS tm)
      = updateHoleUsage useVar var zs tm
  updateHoleUsageScope useVar (MkVar var) zs (Arg c x sc)
      = updateHoleUsageScope useVar (MkVar (Later var)) (map weaken zs) sc

  updateHoleUsageAlt : {vars : _} ->
                    (useVar : Bool) ->
                    Var vars ->
                    List (Var vars) ->
                    CaseAlt vars -> Core Bool
  updateHoleUsageAlt useVar var zs (ConCase fc n t sc)
      = updateHoleUsageScope useVar var zs sc
  updateHoleUsageAlt useVar (MkVar var) zs (DelayCase fc n t sc)
      = updateHoleUsage useVar (MkVar (Later (Later var)))
                        (map (weakenNs (suc (suc zero))) zs) sc
  updateHoleUsageAlt useVar var zs (ConstCase fc c sc)
      = updateHoleUsage useVar var zs sc
  updateHoleUsageAlt useVar var zs (DefaultCase fc sc)
      = updateHoleUsage useVar var zs sc

  updateHoleUsageAlts : {vars : _} ->
                    (useVar : Bool) ->
                    Var vars ->
                    List (Var vars) ->
                    List (CaseAlt vars) -> Core Bool
  updateHoleUsageAlts useVar var zs [] = pure False
  updateHoleUsageAlts useVar var zs (a :: as)
      = do h <- updateHoleUsageAlt useVar var zs a
           h' <- updateHoleUsageAlts useVar var zs as
           pure (h || h')

  -- The assumption here is that hole types are abstracted over the entire
  -- environment, so that they have the appropriate number of function
  -- arguments and there are no lets
  updateHoleType : {vars : _} ->
                   (useVar : Bool) ->
                   Var vars -> List (Var vars) ->
                   Term vs -> List (Term vars) ->
                   Core (Term vs)
  updateHoleType useVar var zs (Bind bfc nm (Pi fc' c e ty) sc) (Local _ r v _ :: as)
      -- if the argument to the hole type is the variable of interest,
      -- and the variable should be used in the hole, leave multiplicity alone,
      -- otherwise set it to erased
      = if varIdx var == v
           then do scty <- updateHoleType False var zs sc as
                   let c' = if useVar then c else erased
                   pure (Bind bfc nm (Pi fc' c' e ty) scty)
           else if elem v (map varIdx zs)
                then do scty <- updateHoleType useVar var zs sc as
                        pure (Bind bfc nm (Pi fc' erased e ty) scty)
                else do scty <- updateHoleType useVar var zs sc as
                        pure (Bind bfc nm (Pi fc' c e ty) scty)
  updateHoleType useVar var zs (Bind bfc nm (Pi fc' c e ty) sc) (a :: as)
      = do ignore $ updateHoleUsage False var zs a
           scty <- updateHoleType useVar var zs sc as
           pure (Bind bfc nm (Pi fc' c e ty) scty)
  updateHoleType useVar var zs ty as
      = do ignore $ updateHoleUsageArgs False var zs as
           pure ty

  updateHoleUsage useVar (MkVar var) zs (Bind _ _ (Let _ _ val _) sc)
      = do h <- updateHoleUsage useVar (MkVar var) zs val
           h' <- updateHoleUsage useVar (MkVar (Later var)) (map weaken zs) sc
           pure (h || h')
  updateHoleUsage useVar (MkVar var) zs (Bind _ n b sc)
      = updateHoleUsage useVar (MkVar (Later var)) (map weaken zs) sc
  updateHoleUsage useVar var zs (Meta fc n i args)
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
                | Nothing => updateHoleUsageArgs useVar var zs (map snd args)
           -- only update for holes with no definition yet
           case definition gdef of
                Hole _ =>
                   do let ty = type gdef
                      ty' <- updateHoleType useVar var zs ty (map snd args)
                      updateTy i ty'
                      logTerm "quantity.hole.update" 5 ("New type of " ++
                                 show (fullname gdef)) ty'
                      logTerm "quantity.hole.update" 5 ("Updated from " ++
                                 show (fullname gdef)) (type gdef)
                      pure True
                _ => updateHoleUsageArgs useVar var zs (map snd args)
  updateHoleUsage useVar var zs (Case _ _ sc scTy alts)
      = do hsc <- updateHoleUsage useVar var zs sc
           hscTy <- updateHoleUsage useVar var zs scTy
           halts <- updateHoleUsageAlts useVar var zs alts
           pure (hsc || hscTy || halts)
  updateHoleUsage useVar var zs (As _ _ a p)
      = updateHoleUsage useVar var zs p
  updateHoleUsage useVar var zs (TDelayed _ _ t)
      = updateHoleUsage useVar var zs t
  updateHoleUsage useVar var zs (TDelay _ _ _ t)
      = updateHoleUsage useVar var zs t
  updateHoleUsage useVar var zs (TForce _ _ t)
      = updateHoleUsage useVar var zs t

  updateHoleUsage useVar var zs tm
      = case getFnArgs tm of
             (Ref _ _ fn, args) =>
                  -- no need to look inside 'fn' for holes since we did that
                  -- when working through lcheckDef recursively
                  updateHoleUsageArgs useVar var zs args
             (f, []) => pure False
             (f, args) => updateHoleUsageArgs useVar var zs (f :: args)

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
  lcheckAlt scrig rig env (ConCase fc n t sc)
      = lcheckScope env sc
    where
      lcheckScope : {vars : _} -> Env Term vars -> CaseScope vars ->
                    Core (Usage vars)
      lcheckScope env (RHS tm) = lcheck rig env tm
      lcheckScope env (Arg c x sc)
            -- We don't have the type of the argument, but the good news is
            -- that we don't need it because we only need multiplicities and
            -- they are cached in App nodes.
          = do let env'
                   = env :<
                     PVar fc (rigMult scrig c) Explicit (Erased fc False)
               u' <- lcheckScope env' sc
               let used = count 0 u'
               checkUsageOK EmptyFC used x (rigMult scrig c)
               pure (doneScope u')
  lcheckAlt scrig rig env (DelayCase fc t a rhs)
      = do -- See above for why the types are erased
           let env'
               = env :<
                 PVar fc erased Implicit (Erased fc False) :<
                 PVar fc scrig Explicit (Erased fc False)
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
  lcheckBinder rig env (Lam fc c p ty) = pure [<]
  lcheckBinder rig env (Let fc c val ty) = lcheck (rigMult rig c) env val
  lcheckBinder rig env (Pi fc c p ty) = lcheck (rigMult rig c) env ty
  lcheckBinder rig env (PVar fc c p ty) = pure [<]
  lcheckBinder rig env (PLet fc c val ty) = lcheck (rigMult rig c) env val
  lcheckBinder rig env (PVTy fc c ty) = pure [<]

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
  lcheck rig env (Meta fc n i args)
      -- If the metavariable is defined, check as normal (we assume that
      -- quantities cached in the arguments have been set appropriately when
      -- the metavariable was resolved).
      -- Otherwise, we don't count variable usage and update the type of the
      -- metavar when leaving the current scope, to show that any linear
      -- things are still available.
      = do defs <- get Ctxt
           let defined
                 = case !(lookupCtxtExact (Resolved i) (gamma defs)) of
                        Nothing => False
                        Just def => case definition def of
                                         Function _ _ => True
                                         _ => False
           if defined
              then do us <- traverse (\ (c, arg) => lcheck (rigMult rig c) env arg) args
                      pure (concat us)
              else pure [<]
  lcheck rig_in env (Bind fc nm b sc)
      = do ub <- lcheckBinder rig env b

           -- Anything linear can't be used in the scope of a let/lambda, if
           -- we're checking in general context
           let (env', rig') = case b of
                                   Pi _ _ _ _ => (env, rig)
                                   _ => (restrictEnv env rig, presence rig)

           usc <- lcheck rig' (env' :< b) sc
           let used_in = count 0 usc

           -- Look for holes in the scope, if the variable is linearly bound.
           -- If the variable hasn't been used, we assume it is to be used in
           -- any holes in the scope of the binder (this is so when a user
           -- inspects the type, they see there is 1 usage available).
           -- 'updateHoleUsage' updates the type of any holes to reflect
           -- whether the variable in question is usable or not.
           holeFound <- if isLinear (multiplicity b)
                           then updateHoleUsage (used_in == 0)
                                         (MkVar First)
                                         (map weaken (getZeroes env'))
                                         sc
                           else pure False

           -- The final usage count is always 1 if the bound variable is
           -- linear and there are holes. Otherwise, we take the count we
           -- found above.
           let used = if isLinear (rigMult (multiplicity b) rig') &&
                         holeFound && used_in == 0
                         then 1
                         else used_in

           checkUsageOK fc used nm (rigMult (multiplicity b) rig')
           pure (ub ++ doneScope usc)
    where
      rig : RigCount
      rig = case b of
                 Pi _ _ _ _ =>
                      if isErased rig_in
                         then erased
                         else top -- checking as if an inspectable run-time type
                 _ => rig_in

      getZeroes : {vs : _} -> Env Term vs -> List (Var vs)
      getZeroes [<] = []
      getZeroes (bs :< b)
          = if isErased (multiplicity b)
               then MkVar First :: map weaken (getZeroes bs)
               else map weaken (getZeroes bs)

  lcheck rig env (App fc fn q arg)
      = do uf <- lcheck rig env fn
           ua <- lcheck (rigMult rig q) env arg
           pure (uf ++ ua)
  lcheck rig env (As fc s var pat)
      = lcheck rig env pat
  lcheck rig env (Case fc scrig sc ty alts)
      = do usc <- lcheck scrig env sc
           ualts <- lcheckAlts rig rig env alts
           pure (usc ++ ualts)
  lcheck rig env (TDelayed fc r tm) = lcheck rig env tm
  lcheck rig env (TDelay fc r ty arg) = lcheck rig env arg
  lcheck rig env (TForce fc r tm) = lcheck rig env tm
  lcheck rig env (PrimVal fc c) = pure [<]
  lcheck rig env (PrimOp fc fn args)
     = do us <- traverseVect (lcheck rig env) args
          pure (concat (toList us))
  lcheck rig env (Erased _ _) = pure [<]
  lcheck rig env (Unmatched _ _) = pure [<]
  lcheck rig env (Impossible _) = pure [<]
  lcheck rig env (TType _ _) = pure [<]

  checkEnvUsage : {vars, done : _} ->
                  FC -> RigCount ->
                  Env Term vars -> Usage (vars ++ done) ->
                  Term (vars ++ done) ->
                  Core ()
  checkEnvUsage fc rig [<] usage tm = pure ()
  checkEnvUsage {done} {vars = xs :< nm} fc rig (bs :< b) usage tm
      = do let pos = localPrf {later=done} {vars=xs} {n=nm}
           let used_in = count (varIdx pos) usage
           -- Adjust usage count depending on holes, as we do when
           -- checking binders
           holeFound <- if isLinear (multiplicity b)
                           then updateHoleUsage (used_in == 0) pos [] tm
                           else pure False
           let used = if isLinear (rigMult (multiplicity b) rig) &&
                         holeFound && used_in == 0
                         then 1
                         else used_in
           checkUsageOK fc used nm (rigMult (multiplicity b) rig)
           checkEnvUsage {done = [<nm] ++ done} fc rig bs
                   (rewrite appendAssociative xs [<nm] done in usage)
                   (rewrite appendAssociative xs [<nm] done in tm)

  export
  linearCheck : {vars : _} ->
                FC -> RigCount -> Env Term vars -> Term vars -> Core ()
  linearCheck fc rig env tm
      = do used <- lcheck rig env tm
           checkEnvUsage {done = [<]} fc rig env used tm
