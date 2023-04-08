module Core.Unify.SolveMeta

-- Machinery for solving and instantiating metavariables, including
-- pattern unification rule and occurs check

import Core.Core
import Core.Context
import Core.Context.Log
import Core.TT
import Core.Evaluate
import Core.Unify.State

import Data.List
import Data.SnocList
import Data.Vect

import Libraries.Data.IntMap
import Libraries.Data.NameMap

-- Get the variables in an application argument list; fail if any arguments
-- are not variables, fail if there's any repetition of variables
-- We use this to check that the pattern unification rule is applicable
-- when solving a metavariable applied to arguments
-- ASSUMPTION: VApp has been reduced first
getVars : {vars : _} ->
          List Nat -> SnocList (NF vars) -> Maybe (SnocList (Var vars))
getVars got [<] = Just [<]
getVars got (xs :< VLocal fc idx v [<])
    = if inArgs idx got then Nothing
         else do xs' <- getVars (idx :: got) xs
                 pure (xs' :< MkVar v)
  where
    -- Save the overhead of the call to APPLY, and the fact that == on
    -- Nat is linear time in Idris 1!
    inArgs : Nat -> List Nat -> Bool
    inArgs n [] = False
    inArgs n (n' :: ns)
        = natToInteger n == natToInteger n' || inArgs n ns
getVars got (xs :< VAs _ _ _ p) = getVars got (xs :< p)
getVars _ (xs :< _) = Nothing

getVarsTm : List Nat -> SnocList (Term vars) -> Maybe (SnocList (Var vars))
getVarsTm got [<] = Just [<]
getVarsTm got (xs :< Local fc idx v)
    = if idx `elem` got then Nothing
         else do xs' <- getVarsTm (idx :: got) xs
                 pure (xs' :< MkVar v)
getVarsTm _ (xs :< _) = Nothing

-- Make a sublist representing the variables used in the application.
-- We'll use this to ensure that local variables which appear in a term
-- are all arguments to a metavariable application for pattern unification
toSubVars : (vars : SnocList Name) -> SnocList (Var vars) ->
            (newvars ** SubVars newvars vars)
toSubVars [<] xs = ([<] ** SubRefl)
toSubVars (ns :< n) xs
     -- If there's a proof 'First' in 'xs', then 'n' should be kept,
     -- otherwise dropped
     -- (Remember: 'n' might be shadowed; looking for 'First' ensures we
     -- get the *right* proof that the name is in scope!)
     = let (_ ** svs) = toSubVars ns (dropFirst xs) in
           if anyFirst xs
              then (_ ** KeepCons svs)
              else (_ ** DropCons svs)
  where
    anyFirst : SnocList (Var (ns :< n)) -> Bool
    anyFirst [<] = False
    anyFirst (xs :< MkVar First) = True
    anyFirst (xs :< MkVar (Later p)) = anyFirst xs

-- How the variables in a metavariable definition map to the variables in
-- the solution term (the Var newvars)
data IVars : SnocList Name -> SnocList Name -> Type where
     INil : IVars [<] newvars
     ICons : Maybe (Var newvars) -> IVars vs newvars ->
             IVars (vs :< v) newvars

Weaken (IVars vs) where
  weaken INil = INil
  weaken (ICons Nothing ts) = ICons Nothing (weaken ts)
  weaken (ICons (Just t) ts) = ICons (Just (weaken t)) (weaken ts)

getIVars : IVars vs ns -> List (Maybe (Var ns))
getIVars INil = []
getIVars (ICons v vs) = v :: getIVars vs

parameters {auto c : Ref Ctxt Defs} {auto c : Ref UST UState}
  -- Find all the metavariables required by each of the given names.
  -- We'll assume all meta solutions are of the form STerm exp.
  chaseMetas : List Name -> NameMap () -> Core (List Name)
  chaseMetas [] all = pure (keys all)
  chaseMetas (n :: ns) all
      = case lookup n all of
             Just _ => chaseMetas ns all
             _ => do defs <- get Ctxt
                     Just (Function _ soln _ _) <- lookupDefExact n (gamma defs)
                          | _ => chaseMetas ns (insert n () all)
                     let sns = keys (getMetas soln)
                     chaseMetas (sns ++ ns) (insert n () all)

  -- Get all the metavariable names used by the term (recursively, so we
  -- can do the occurs check)
  getMetaNames : Term vars -> Core (List Name)
  getMetaNames tm
      = let metas = getMetas tm in
            chaseMetas (keys metas) empty
  {- Applying the pattern unification rule is okay if:
     * Arguments are all distinct local variables
     * The metavariable name doesn't appear in the unifying term
     * The local variables which appear in the term are all arguments to
       the metavariable application (not checked here, checked with the
       result of `patternEnv`)

     Return the subset of the environment used in the arguments
     to which the metavariable is applied. If this environment is enough
     to check the term we're unifying with, and that term doesn't use the
     metavariable name, we can safely apply the rule.

     Also, return the list of arguments the metavariable was applied to, to
     make sure we use them in the right order when we build the solution.
  -}
  export
  patternEnv : {vars : _} ->
               Env Term vars -> SnocList (Glued vars) ->
               Core (Maybe (newvars ** (SnocList (Var newvars),
                                       SubVars newvars vars)))
  patternEnv {vars} env args
      = do -- Make sure the arguments are evaluated enough to know whether
           -- they're variables (this is an assumption made by getVars)
           args' <- traverseSnocList expand args
           pure $ case getVars [] args' of
                 Nothing => Nothing
                 Just vs =>
                   let (newvars ** svs) = toSubVars _ vs in
                     Just (newvars ** (updateVars vs svs, svs))
    where
      -- Update the variable list to point into the sub environment
      -- (All of these will succeed because the SubVars we have comes from
      -- the list of variable uses! It's not stated in the type, though.)
      updateVars : SnocList (Var vars) -> SubVars newvars vars ->
                   SnocList (Var newvars)
      updateVars [<] svs = [<]
      updateVars (ps :< MkVar p) svs
          = case subElem p svs of
                 Nothing => updateVars ps svs
                 Just p' => updateVars ps svs :< p'

  export
  patternEnvTm : {vars : _} ->
                 Env Term vars -> SnocList (Term vars) ->
                 Core (Maybe (newvars ** (SnocList (Var newvars),
                                         SubVars newvars vars)))
  patternEnvTm {vars} env args
      = pure $ case getVarsTm [] args of
             Nothing => Nothing
             Just vs =>
               let (newvars ** svs) = toSubVars _ vs in
                   Just (newvars ** (updateVars vs svs, svs))
    where
      -- Update the variable list to point into the sub environment
      -- (All of these will succeed because the SubVars we have comes from
      -- the list of variable uses! It's not stated in the type, though.)
      updateVars : SnocList (Var vars) -> SubVars newvars vars -> SnocList (Var newvars)
      updateVars [<] svs = [<]
      updateVars (ps :< MkVar p) svs
          = case subElem p svs of
                 Nothing => updateVars ps svs
                 Just p' => updateVars ps svs :< p'

  -- Check that the metavariable name doesn't occur in the solution.
  -- If it does, normalising might help. If it still does, that's an error.
  export
  occursCheck : {vars : _} ->
                FC -> Env Term vars -> UnifyInfo ->
                Name -> Term vars -> Core (Maybe (Term vars))
  occursCheck fc env mode mname tm
      = do solmetas <- getMetaNames tm
           let False = mname `elem` solmetas
               | _ => do tmnf <- normalise env tm
                         solmetas <- getMetaNames tmnf
                         if mname `elem` solmetas
                            then do failOnStrongRigid False
                                       (throw (CyclicMeta fc env mname tmnf))
                                       tmnf
                                    pure Nothing
                            else pure $ Just tmnf
           pure $ Just tm
    where
      -- Throw an occurs check failure if the name appears 'strong rigid',
      -- that is, under a constructor form rather than a function, in the
      -- term
      failOnStrongRigid : Bool -> Core () -> Term vars -> Core ()
      failOnStrongRigid bad err (Meta _ n _ _)
          = if bad && n == mname
               then err
               else pure ()
      failOnStrongRigid bad err tm
          = case getFnArgs tm of
                 (f, []) => pure ()
                 (Ref _ Func _, _) => pure () -- might reduce away, just block
                 (Ref _ _ _, args) => traverse_ (failOnStrongRigid True err) args
                 (f, args) => traverse_ (failOnStrongRigid bad err) args

  -- Instantiate a metavariable by binding the variables in 'newvars'
  -- and returning the term
  -- If the type of the metavariable doesn't have enough arguments, fail, because
  -- this wasn't valid for pattern unification
  export
  tryInstantiate : {vars, newvars : _} ->
                FC -> UnifyInfo -> Env Term vars ->
                (metavar : Name) -> (mref : Int) -> (numargs : Nat) ->
                (mdef : GlobalDef) ->
                List (Var newvars) -> -- Variable each argument maps to
                Term vars -> -- original, just for error message
                Term newvars -> -- shrunk environment
                Core Bool -- postpone if the type is yet unknown
  tryInstantiate {newvars} loc mode env mname mref num mdef locs otm tm
      = do logTerm "unify.instantiate" 5 ("Instantiating in " ++ show newvars) tm
           case fullname mdef of
                PV pv pi => throw (PatternVariableUnifies loc (getLoc otm) env (PV pv pi) otm)
                _ => pure ()
           defs <- get Ctxt
           -- Make sure any applications are expanded to pi binders, if that's
           -- what they are in the type
           ty <- quoteBinders [<] !(nf [<] (type mdef))
           logTerm "unify.instantiate" 5 ("Type: " ++ show mname) (type mdef)
           logTerm "unify.instantiate" 5 ("Type: " ++ show mname) ty
           log "unify.instantiate" 5 ("With locs: " ++ show locs)
           log "unify.instantiate" 5 ("From vars: " ++ show newvars)

           defs <- get Ctxt
           -- Try to instantiate the hole
           Just rhs <- mkDef locs INil tm ty
             | _ => do
                 log "unify.instantiate" 5 "Postponed"
                 pure False

           logTerm "unify.instantiate" 5 (show mname ++ " definition:") rhs
           let simpleDef = MkFnInfo (SolvedHole num)
                                     (not (isUserName mname) && isSimple rhs)
                                     False
           let newdef = { definition := Function simpleDef rhs rhs Nothing } mdef
           ignore $ addDef (Resolved mref) newdef
           removeHole mref
           pure True
    where
      -- A solution is deemed simple enough to inline if either:
      --   * It is smaller than some threshold and has no metavariables in it
      --   * It's just a metavariable itself
      noMeta : Term vs -> Nat -> Bool
      noMeta (App _ f _ a) (S k) = noMeta f k && noMeta a k
      noMeta (Bind _ _ b sc) (S k) = noMeta (binderType b) k && noMeta sc k
      noMeta (Meta _ _ _ _) d = False
      noMeta (TDelayed _ _ t) d = noMeta t d
      noMeta (TDelay _ _ t a) d = noMeta t d && noMeta a d
      noMeta (TForce _ _ t) d = noMeta t d
      noMeta (As _ _ _ p) d = noMeta p d
      noMeta (Local _ _ _) _ = True
      noMeta (Ref _ _ _) _ = True
      noMeta (PrimVal _ _) _ = True
      noMeta (TType _ _) _ = True
      noMeta _ _ = False

      isSimple : Term vs -> Bool
      isSimple (Meta _ _ _ _) = True
      isSimple (Bind _ _ (Lam _ _ _ _) sc) = isSimple sc
      isSimple (App _ f _ a) = noMeta f 6 && noMeta a 3
      isSimple tm = noMeta tm 0

      updateIVar : {v : Nat} ->
                   forall vs, newvars . IVars vs newvars -> (0 p : IsVar nm v newvars) ->
                   Maybe (Var vs)
      updateIVar {v} (ICons Nothing rest) prf
          = do MkVar prf' <- updateIVar rest prf
               Just (MkVar (Later prf'))
      updateIVar {v} (ICons (Just (MkVar {i} p)) rest) prf
          = if v == i
               then Just (MkVar First)
               else do MkVar prf' <- updateIVar rest prf
                       Just (MkVar (Later prf'))
      updateIVar _ _ = Nothing

      updateIVars : {vs, newvars : _} ->
                    IVars vs newvars -> Term newvars -> Maybe (Term vs)

      updateIScope : {vs, newvars : _} ->
                    IVars vs newvars -> CaseScope newvars -> Maybe (CaseScope vs)
      updateIScope ivs (RHS tm) = Just (RHS !(updateIVars ivs tm))
      updateIScope ivs (Arg c x sc)
          = Just (Arg c x !(updateIScope (ICons (Just (MkVar First))
                                              (weaken ivs)) sc))

      updateIAlts : {vs, newvars : _} ->
                    IVars vs newvars -> CaseAlt newvars -> Maybe (CaseAlt vs)
      updateIAlts ivs (ConCase fc n t sc)
          = Just (ConCase fc n t !(updateIScope ivs sc))
      updateIAlts ivs (DelayCase fc ty arg rhs)
          = let ivs' = ICons (Just (MkVar First)) $
                       ICons (Just (MkVar (Later First))) $
                       weaken (weaken ivs) in
                Just (DelayCase fc ty arg !(updateIVars ivs' rhs))
      updateIAlts ivs (ConstCase fc c rhs)
          = Just (ConstCase fc c !(updateIVars ivs rhs))
      updateIAlts ivs (DefaultCase fc rhs)
          = Just (DefaultCase fc !(updateIVars ivs rhs))

      updateIVars ivs (Local fc idx p)
          = do MkVar p' <- updateIVar ivs p
               Just (Local fc _ p')
      updateIVars ivs (Ref fc nt n) = pure $ Ref fc nt n
      updateIVars ivs (Meta fc n i args)
          = pure $ Meta fc n i
                        !(traverse (\ (c, t) => do t' <- updateIVars ivs t
                                                   pure (c, t')) args)
      updateIVars {vs} ivs (Bind fc x b sc)
          = do b' <- updateIVarsB ivs b
               sc' <- updateIVars (ICons (Just (MkVar First)) (weaken ivs)) sc
               Just (Bind fc x b' sc')
        where
          updateIVarsPi : {vs, newvars : _} ->
                          IVars vs newvars -> PiInfo (Term newvars) -> Maybe (PiInfo (Term vs))
          updateIVarsPi ivs Explicit = Just Explicit
          updateIVarsPi ivs Implicit = Just Implicit
          updateIVarsPi ivs AutoImplicit = Just AutoImplicit
          updateIVarsPi ivs (DefImplicit t)
              = do t' <- updateIVars ivs t
                   Just (DefImplicit t')

          updateIVarsB : {vs, newvars : _} ->
                         IVars vs newvars -> Binder (Term newvars) -> Maybe (Binder (Term vs))
          updateIVarsB ivs (Lam fc c p t)
              = do p' <- updateIVarsPi ivs p
                   Just (Lam fc c p' !(updateIVars ivs t))
          updateIVarsB ivs (Let fc c v t) = Just (Let fc c !(updateIVars ivs v) !(updateIVars ivs t))
          -- Make 'pi' binders have multiplicity W when we infer a Rig1 metavariable,
          -- since this is the most general thing to do if it's unknown.
          updateIVarsB ivs (Pi fc rig p t)
              = do p' <- updateIVarsPi ivs p
                   Just (Pi fc rig p' !(updateIVars ivs t))
          updateIVarsB ivs (PVar fc c p t)
              = do p' <- updateIVarsPi ivs p
                   Just (PVar fc c p' !(updateIVars ivs t))
          updateIVarsB ivs (PLet fc c v t) = Just (PLet fc c !(updateIVars ivs v) !(updateIVars ivs t))
          updateIVarsB ivs (PVTy fc c t) = Just (PVTy fc c !(updateIVars ivs t))
      updateIVars ivs (App fc f c a)
          = Just (App fc !(updateIVars ivs f) c !(updateIVars ivs a))
      updateIVars ivs (As fc u as p)
          = Just (As fc u !(updateIVars ivs as) !(updateIVars ivs p))
      updateIVars ivs (Case fc t c sc scty alts)
          = Just (Case fc t c !(updateIVars ivs sc) !(updateIVars ivs scty)
                       !(traverse (updateIAlts ivs) alts))
      updateIVars ivs (TDelayed fc r arg)
          = Just (TDelayed fc r !(updateIVars ivs arg))
      updateIVars ivs (TDelay fc r ty arg)
          = Just (TDelay fc r !(updateIVars ivs ty) !(updateIVars ivs arg))
      updateIVars ivs (TForce fc r arg)
          = Just (TForce fc r !(updateIVars ivs arg))
      updateIVars ivs (PrimVal fc c) = Just (PrimVal fc c)
      updateIVars ivs (PrimOp fc fn args)
          = Just (PrimOp fc fn !(traverse (updateIVars ivs) args))
      updateIVars ivs (Erased fc why) = Erased fc <$> traverse (updateIVars ivs) why
      updateIVars ivs (Unmatched fc s) = Just (Unmatched fc s)
      updateIVars ivs (TType fc u) = Just (TType fc u)

      mkDef : {vs, newvars : _} ->
              List (Var newvars) ->
              IVars vs newvars -> Term newvars -> Term vs ->
              Core (Maybe (Term vs))
      mkDef (v :: vs) vars soln (Bind bfc x (Pi fc c _ ty) sc)
         = do sc' <- mkDef vs (ICons (Just v) vars) soln sc
              pure $ (Bind bfc x (Lam fc c Explicit (Erased bfc Placeholder)) <$> sc')
      mkDef vs vars soln (Bind bfc x b@(Let _ c val ty) sc)
         = do mbsc' <- mkDef vs (ICons Nothing vars) soln sc
              flip traverseOpt mbsc' $ \sc' =>
                case shrinkTerm sc' (DropCons SubRefl) of
                  Just scs => pure scs
                  Nothing => pure $ Bind bfc x b sc'
      mkDef [] vars soln _
         = do let Just soln' = updateIVars vars soln
                  | Nothing => ufail loc ("Can't make solution for " ++ show mname
                                             ++ " " ++ show (getIVars vars, soln))
              pure (Just soln')
      mkDef _ _ _ _ = pure Nothing

  -- update a solution that the machine found with the thing the programmer
  -- actually wrote! We assume that we've already checked that they unify.
  export
  updateSolution : {vars : _} ->
                   Env Term vars -> Term vars -> Term vars -> Core Bool
  updateSolution env (Meta fc mname idx args) soln
      = do defs <- get Ctxt
           case !(patternEnvTm env (cast (map snd args))) of
                Nothing => pure False
                Just (newvars ** (locs, submv)) =>
                    case shrinkTerm soln submv of
                         Nothing => pure False
                         Just stm =>
                            do Just hdef <- lookupCtxtExact (Resolved idx) (gamma defs)
                                    | Nothing => throw (InternalError "Can't happen: no definition")
                               tryInstantiate fc inTerm env mname idx (length args) hdef (toList locs) soln stm
  updateSolution env metavar soln
      = pure False

  export
  solveIfUndefined : {vars : _} ->
                     Env Term vars -> Term vars -> Term vars -> Core Bool
  solveIfUndefined env metavar@(Meta fc mname idx args) soln
      = do defs <- get Ctxt
           Just (Hole _ _) <- lookupDefExact (Resolved idx) (gamma defs)
                | _ => pure False
           updateSolution env metavar soln
  solveIfUndefined env (Erased _ (Dotted metavar)) soln
    = solveIfUndefined env metavar soln
  solveIfUndefined env metavar soln
      = pure False
