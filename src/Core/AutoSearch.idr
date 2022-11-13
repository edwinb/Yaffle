module Core.AutoSearch

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Evaluate
import Core.TT
import Core.Unify
import Core.Unify.SolveMeta

import Data.Either
import Data.List
import Data.Maybe
import Data.SnocList

%default covering

searchType : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             FC -> RigCount ->
             (defaults : Bool) -> (trying : List (Term vars)) ->
             (depth : Nat) ->
             (defining : Name) ->
             (checkDets : Bool) -> (topTy : ClosedTerm) ->
             Env Term vars -> (target : Term vars) -> Core (Term vars)

public export
record ArgInfo (vars : SnocList Name) where
  constructor MkArgInfo
  holeID : Int
  argRig : RigCount
  plicit : PiInfo (Glued vars)
  metaApp : (RigCount, Term vars)
  argType : Term vars

export
mkArgs : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         FC -> RigCount ->
         Env Term vars -> NF vars ->
         Core (List (ArgInfo vars), NF vars)
mkArgs fc rigc env (VBind nfc x (Pi fc' c p ty) sc)
    = do defs <- get Ctxt
         nm <- genName "sa"
         argTy <- quote env ty
         let argRig = rigMult rigc c
         (idx, arg) <- newMeta fc' argRig env nm argTy
                               (Hole (length env) (holeInit False))
         argVal <- nf env arg
         setInvertible fc (Resolved idx)
         (rest, restTy) <- mkArgs fc rigc env !(expand !(sc argVal))
         pure (MkArgInfo idx argRig p (c, arg) argTy :: rest, restTy)
mkArgs fc rigc env ty = pure ([], ty)

export
impLast : List (ArgInfo vars) -> List (ArgInfo vars)
impLast xs = filter (not . impl) xs ++ filter impl xs
  where
      impl : ArgInfo vs -> Bool
      impl inf
          = case plicit inf of
                 Explicit => False
                 _ => True

searchIfHole : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               FC ->
               (defaults : Bool) -> List (Term vars) ->
               (ispair : Bool) -> (depth : Nat) ->
               (defining : Name) -> (topTy : ClosedTerm) -> Env Term vars ->
               (arg : ArgInfo vars) ->
               Core ()
searchIfHole fc defaults trying ispair Z def top env arg
    = throw (CantSolveGoal fc !(get Ctxt) [<] top Nothing) -- possibly should say depth limit hit?
searchIfHole fc defaults trying ispair (S depth) def top env arg
    = do let hole = holeID arg
         let rig = argRig arg

         defs <- get Ctxt
         Just gdef <- lookupCtxtExact (Resolved hole) (gamma defs)
              | Nothing => throw (CantSolveGoal fc !(get Ctxt) [<] top Nothing)
         let Hole _ _ = definition gdef
              | _ => pure () -- already solved
         top' <- if ispair
                    then normaliseScope [<] (type gdef)
                    else pure top

         argdef <- searchType fc rig defaults trying depth def False top' env
                              !(normaliseScope env (argType arg))
         logTermNF "auto" 5 "Solved arg" env argdef
         logTermNF "auto" 5 "Arg meta" env (snd (metaApp arg))
         ok <- solveIfUndefined env (snd (metaApp arg)) argdef
         if ok
            then pure ()
            else do vs <- unify inTerm fc env (snd (metaApp arg)) argdef
                    let [] = constraints vs
                        | _ => throw (CantSolveGoal fc defs [<] top Nothing)
                    pure ()

successful : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             List (Core (Term vars)) ->
             Core (List (Either Error (Term vars, Defs, UState)))
successful [] = pure []
successful (elab :: elabs)
    = do ust <- get UST
         defs <- branch
         catch (do -- Run the elaborator
                   res <- elab
                   -- Record post-elaborator state
                   ust' <- get UST
                   defs' <- get Ctxt
                   -- Reset to previous state and try the rest
                   put UST ust
                   put Ctxt defs
                   elabs' <- successful elabs
                   -- Record success, and the state we ended at
                   pure (Right (res, defs', ust') :: elabs'))
               (\err => do put UST ust
                           put Ctxt defs
                           elabs' <- successful elabs
                           pure (Left err :: elabs'))

anyOne : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         FC -> Env Term vars -> (topTy : ClosedTerm) ->
         List (Core (Term vars)) ->
         Core (Term vars)
anyOne fc env top [] = throw (CantSolveGoal fc !(get Ctxt) [<] top Nothing)
anyOne fc env top [elab]
    = catch elab $
         \case
           err@(CantSolveGoal _ _ _ _ _) => throw err
           _ => throw $ CantSolveGoal fc !(get Ctxt) [<] top Nothing
anyOne fc env top (elab :: elabs)
    = tryUnify elab (anyOne fc env top elabs)

exactlyOne : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             FC -> Env Term vars -> (topTy : ClosedTerm) -> (target : NF vars) ->
             List (Core (Term vars)) ->
             Core (Term vars)
exactlyOne fc env top target [elab]
    = catch elab $
         \case
           err@(CantSolveGoal _ _ _ _ _) => throw err
           _ => throw $ CantSolveGoal fc !(get Ctxt) [<] top Nothing
exactlyOne {vars} fc env top target all
    = do elabs <- successful all
         case rights elabs of
              [(res, defs, ust)] =>
                    do put UST ust
                       put Ctxt defs
                       commit
                       pure res
              [] => throw (CantSolveGoal fc !(get Ctxt) [<] top Nothing)
              rs => throw (AmbiguousSearch fc env !(quote env target)
                             !(traverse normRes rs))
  where
    normRes : (Term vars, Defs, UState) -> Core (Term vars)
    normRes (tm, defs, _)
        = do olddefs <- get Ctxt
             put Ctxt defs
             res <- normaliseHoles env tm
             put Ctxt olddefs
             pure res

-- We can only resolve things which are at unrestricted multiplicity. Expression
-- search happens before linearity checking and we can't guarantee that just
-- because something is apparently available now, it will be available by the
-- time we get to linearity checking.
-- It's also fine to use anything if we're working at multiplicity 0
getUsableEnv : {vars : _} ->
                FC -> RigCount ->
                SizeOf done ->
                Env Term vars ->
                List (Term (vars ++ done), Term (vars ++ done))
getUsableEnv fc rigc p [<] = []
getUsableEnv {vars = vs :< v} {done} fc rigc p (env :< b)
   = let rest = getUsableEnv fc rigc (sucR p) env in
         if (multiplicity b == top || isErased rigc)
            then let MkVar var = weakenVar p (MkVar First) in
                     (Local (binderLoc b) Nothing _ var,
                       rewrite sym (appendAssociative vs [<v] done) in
                          weakenNs (sucR p) (binderType b)) ::
                            rewrite sym (appendAssociative vs [<v] done) in rest
            else rewrite sym (appendAssociative vs [<v] done) in rest

-- A local is usable if it contains no holes in a determining argument position
usableLocal : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              FC -> (defaults : Bool) ->
              Env Term vars -> (locTy : NF vars) -> Core Bool
-- pattern variables count as concrete things!
usableLocal loc defaults env (VMeta fc (PV _ _) _ _ _ _)
    = pure True
usableLocal loc defaults env (VMeta{})
    = pure False
usableLocal {vars} loc defaults env (VTCon _ n _ args)
    = do sd <- getSearchData loc (not defaults) n
         usableLocalArg 0 (detArgs sd) (cast (map spineArg args))
  -- usable if none of the determining arguments of the local's type are
  -- holes
  where
    usableLocalArg : Nat -> List Nat -> List (Glued vars) -> Core Bool
    usableLocalArg i dets [] = pure True
    usableLocalArg i dets (arg :: args)
        = if i `elem` dets
             then do defs <- get Ctxt
                     u <- usableLocal loc defaults env !(expand arg)
                     if u
                        then usableLocalArg (1 + i) dets args
                        else pure False
             else usableLocalArg (1 + i) dets args
usableLocal loc defaults env (VDCon _ n _ _ args)
    = do us <- traverseSnocList (usableLocal loc defaults env)
                        !(traverseSnocList spineVal args)
         pure (all id us)
usableLocal loc defaults env (VLocal _ _ _ _ args)
    = do us <- traverseSnocList (usableLocal loc defaults env)
                        !(traverseSnocList spineVal args)
         pure (all id us)
usableLocal loc defaults env (VBind fc x (Pi _ _ _ _) sc)
    = usableLocal loc defaults env !(expand !(sc (VErased fc Placeholder)))
usableLocal loc defaults env (VErased _ _) = pure False
usableLocal loc _ _ _ = pure True

searchLocalWith : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  FC -> RigCount ->
                  (defaults : Bool) -> List (Term vars) ->
                  (depth : Nat) ->
                  (defining : Name) -> (topTy : ClosedTerm) ->
                  Env Term vars -> (Term vars, Term vars) ->
                  (target : NF vars) -> Core (Term vars)
searchLocalWith {vars} fc rigc defaults trying depth def top env (prf, ty) target
    = do nty <- nf env ty
         findPos prf id !(expand nty) target
  where
    ambig : Error -> Bool
    ambig (AmbiguousSearch _ _ _ _) = True
    ambig _ = False

    clearEnvType : {idx : Nat} -> (0 p : IsVar nm idx vs) ->
                   FC -> Env Term vs -> Env Term vs
    clearEnvType First fc (env :< b)
        = env :<
           Lam (binderLoc b) (multiplicity b) Explicit (Erased fc Placeholder)
    clearEnvType (Later p) fc (env :< b) = clearEnvType p fc env :< b

    clearEnv : Term vars -> Env Term vars -> Env Term vars
    clearEnv (Local fc _ idx p) env
        = clearEnvType p fc env
    clearEnv _ env = env

    findDirect : Term vars ->
                 (Term vars -> Term vars) ->
                 NF vars ->  -- local's type
                 (target : NF vars) ->
                 Core (Term vars)
    findDirect p f ty target
        = do (args, appTy) <- mkArgs fc rigc env ty
             logTermNF "auto" 10 "Trying" env (f prf)
             logNF "auto" 10 "Type" env ty
             logNF "auto" 10 "For target" env target
             defs <- get Ctxt
             ures <- unify inTerm fc env target appTy
             let [] = constraints ures
                 | _ => throw (CantSolveGoal fc defs [<] top Nothing)
             -- We can only use the local if its type is not an unsolved hole
             if !(usableLocal fc defaults env ty)
                then do
                   let candidate = apply fc (f prf) (map metaApp args)
                   logTermNF "auto" 10 "Local var candidate " env candidate
                   -- Clear the local from the environment to avoid getting
                   -- into a loop repeatedly applying it
                   let env' = clearEnv prf env
                   -- Work right to left, because later arguments may solve
                   -- earlier ones by unification
                   traverse_ (searchIfHole fc defaults trying False depth def top env')
                            (impLast args)
                   pure candidate
                else do logNF "auto" 10 "Can't use " env ty
                        throw (CantSolveGoal fc defs [<] top Nothing)

    findPos : Term vars ->
              (Term vars -> Term vars) ->
              NF vars ->  -- local's type
              (target : NF vars) ->
              Core (Term vars)
    findPos p f nty@(VTCon pfc pn _ [< (_, (xc, xty)), (_, (yc, yty))]) target
        = handleUnify (findDirect prf f nty target) (\e =>
           if ambig e then throw e else
             do defs <- get Ctxt
                fname <- maybe (throw (CantSolveGoal fc defs [<] top Nothing))
                               pure
                               !fstName
                sname <- maybe (throw (CantSolveGoal fc defs [<] top Nothing))
                               pure
                               !sndName
                if !(isPairType pn)
                   then do xtytm <- quote env xty
                           ytytm <- quote env yty
                           exactlyOne fc env top target
                            [(do xtynf <- expand xty
                                 findPos p
                                     (\arg => apply fc (Ref fc Func fname)
                                                        [(xc, xtytm),
                                                         (yc, ytytm),
                                                         (RigCount.top, f arg)])
                                     xtynf target),
                             (do ytynf <- expand yty
                                 findPos p
                                     (\arg => apply fc (Ref fc Func sname)
                                                        [(xc, xtytm),
                                                         (yc, ytytm),
                                                         (RigCount.top, f arg)])
                                     ytynf target)]
                   else throw (CantSolveGoal fc defs [<] top Nothing))
    findPos p f nty target
        = findDirect p f nty target

searchLocalVars : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  FC -> RigCount ->
                  (defaults : Bool) -> List (Term vars) ->
                  (depth : Nat) ->
                  (defining : Name) -> (topTy : ClosedTerm) ->
                  Env Term vars ->
                  (target : NF vars) -> Core (Term vars)
searchLocalVars fc rig defaults trying depth def top env target
    = do let elabs = map (\t => searchLocalWith fc rig defaults trying depth def
                                              top env t target)
                         (getUsableEnv fc rig zero env)
         exactlyOne fc env top target elabs

isPairNF : {auto c : Ref Ctxt Defs} ->
           Env Term vars -> NF vars -> Core Bool
isPairNF env (VTCon _ n _ _)
    = isPairType n
isPairNF env (VBind fc b (Pi _ _ _ _) sc)
    = isPairNF env !(expand !(sc (VErased fc Placeholder)))
isPairNF _ _ = pure False

searchName : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             FC -> RigCount ->
             (defaults : Bool) -> List (Term vars) ->
             (depth : Nat) ->
             (defining : Name) -> (topTy : ClosedTerm) ->
             Env Term vars -> (target : NF vars) ->
             (Name, GlobalDef) ->
             Core (Term vars)
searchName fc rigc defaults trying depth def top env target (n, ndef)
    = do defs <- get Ctxt
         when (not (visibleInAny (!getNS :: !getNestedNS)
                                 (fullname ndef) (visibility ndef))) $
            throw (CantSolveGoal fc defs [<] top Nothing)
         when (BlockedHint `elem` flags ndef) $
            throw (CantSolveGoal fc defs [<] top Nothing)

         let ty = type ndef
         let namety : NameType
                 = case definition ndef of
                        DCon _ tag arity => DataCon tag arity
                        TCon ti arity => TyCon arity
                        _ => Func
         nty <- expand !(nf env (embed ty))
         logNF "auto" 10 ("Searching Name " ++ show n) env nty
         (args, appTy) <- mkArgs fc rigc env nty
         ures <- unify inTerm fc env target appTy
         let [] = constraints ures
             | _ => throw (CantSolveGoal fc defs [<] top Nothing)
         ispair <- isPairNF env nty
         let candidate = apply fc (Ref fc namety n) (map metaApp args)
         logTermNF "auto" 10 "Candidate " env candidate
         -- Work right to left, because later arguments may solve earlier
         -- dependencies by unification
         traverse_ (searchIfHole fc defaults trying ispair depth def top env)
                  (impLast args)
         pure candidate

searchNames : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> RigCount ->
              (defaults : Bool) -> List (Term vars) ->
              (depth : Nat) ->
              (defining : Name) -> (topTy : ClosedTerm) ->
              Env Term vars -> Bool -> List Name ->
              (target : NF vars) -> Core (Term vars)
searchNames fc rigc defaults trying depth defining topty env ambig [] target
    = throw (CantSolveGoal fc !(get Ctxt) [<] topty Nothing)
searchNames fc rigc defaults trying depth defining topty env ambig (n :: ns) target
    = do defs <- get Ctxt
         visnsm <- traverse (visible (gamma defs) (currentNS defs :: nestedNS defs)) (n :: ns)
         let visns = mapMaybe id visnsm
         let elabs = map (searchName fc rigc defaults trying depth defining topty env target) visns
         if ambig
            then anyOne fc env topty elabs
            else exactlyOne fc env topty target elabs
  where
    visible : Context ->
              List Namespace -> Name -> Core (Maybe (Name, GlobalDef))
    visible gam nspace n
        = do Just def <- lookupCtxtExact n gam
                  | Nothing => pure Nothing
             if visibleInAny nspace n (visibility def)
                then pure $ Just (n, def)
                else pure $ Nothing

concreteDets : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               FC -> Bool ->
               Env Term vars -> (top : ClosedTerm) ->
               (pos : Nat) -> (dets : List Nat) ->
               (args : List (Glued vars)) ->
               Core ()
concreteDets fc defaults env top pos dets [] = pure ()
concreteDets {vars} fc defaults env top pos dets (arg :: args)
    = do when (pos `elem` dets) $ do
           argnf <- expand arg
           logNF "auto.determining" 10
             "Checking that the following argument is concrete"
             env argnf
           concrete argnf True
         concreteDets fc defaults env top (1 + pos) dets args
  where
    drop : Nat -> List Nat -> List t -> List t
    drop i ns [] = []
    drop i ns (x :: xs)
        = if i `elem` ns
             then x :: drop (1+i) ns xs
             else drop (1+i) ns xs

    concrete : NF vars -> (atTop : Bool) -> Core ()
    concrete (VBind nfc x b sc) atTop
        = do scnf <- expand !(sc (VErased nfc Placeholder))
             concrete scnf False
    concrete (VTCon nfc n a args) atTop
        = do sd <- getSearchData nfc False n
             let args' = drop 0 (detArgs sd) (cast args)
             traverse_ (\ parg => do argnf <- expand parg
                                     concrete argnf False) (map spineArg args')
    concrete (VDCon nfc n t a args) atTop
        = do traverse_ (\ parg => do argnf <- expand parg
                                     concrete argnf False)
                       (map spineArg (cast args))
    concrete (VMeta _ n i _ _ _) True
        = do defs <- get Ctxt
             Just (Hole _ b) <- lookupDefExact n (gamma defs)
                  | _ => throw (DeterminingArg fc n i [<] top)
             unless (implbind b) $
                  throw (DeterminingArg fc n i [<] top)
    concrete (VMeta _ n i _ _ _) False
        = do defs <- get Ctxt
             Just (Hole _ b) <- lookupDefExact n (gamma defs)
                  | def => throw (CantSolveGoal fc defs [<] top Nothing)
             unless (implbind b) $
                  throw (CantSolveGoal fc defs [<] top Nothing)
    concrete tm atTop = pure ()

checkConcreteDets : {vars : _} ->
                    {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST UState} ->
                    FC -> Bool ->
                    Env Term vars -> (top : ClosedTerm) ->
                    NF vars ->
                    Core ()
checkConcreteDets fc defaults env top (VTCon tfc tyn t args)
    = do defs <- get Ctxt
         if !(isPairType tyn)
            then case args of
                      [< (_, (_, aty)), (_, (_, bty))] =>
                          do anf <- expand aty
                             bnf <- expand bty
                             checkConcreteDets fc defaults env top anf
                             checkConcreteDets fc defaults env top bnf
                      _ => do sd <- getSearchData fc defaults tyn
                              concreteDets fc defaults env top 0 (detArgs sd) (cast (map spineArg args))
            else
              do sd <- getSearchData fc defaults tyn
                 log "auto.determining" 10 $
                   "Determining arguments for " ++ show !(toFullNames tyn)
                   ++ " " ++ show (detArgs sd)
                 concreteDets fc defaults env top 0 (detArgs sd) (cast (map spineArg args))
checkConcreteDets fc defaults env top _
    = pure ()

abandonIfCycle : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 Env Term vars -> Term vars -> List (Term vars) ->
                 Core ()
abandonIfCycle env tm [] = pure ()
abandonIfCycle env tm (ty :: tys)
    = do defs <- get Ctxt
         if !(convert env tm ty)
            then throw (InternalError "Cycle in search")
            else abandonIfCycle env tm tys

-- Declared at the top
searchType fc rigc defaults trying depth def checkdets top env (Bind nfc x b@(Pi fc' c p ty) sc)
    = pure (Bind nfc x (Lam fc' c p ty)
             !(searchType fc rigc defaults [] depth def checkdets top
                          (env :< b) sc))
searchType fc rigc defaults trying depth def checkdets top env (Bind nfc x b@(Let fc' c val ty) sc)
    = pure (Bind nfc x b
             !(searchType fc rigc defaults [] depth def checkdets top
                          (env :< b) sc))
searchType {vars} fc rigc defaults trying depth def checkdets top env target
    = do defs <- get Ctxt
         abandonIfCycle env target trying
         let trying' = target :: trying
         nty <- expand !(nf env target)
         case nty of
              VTCon tfc tyn a args =>
                  if a == length args
                     then do logNF "auto" 10 "Next target" env nty
                             sd <- getSearchData fc defaults tyn
                             -- Check determining arguments are okay for 'args'
                             when checkdets $
                                 checkConcreteDets fc defaults env top
                                                   (VTCon tfc tyn a args)
                             if defaults && checkdets
                                then tryGroups Nothing nty (hintGroups sd)
                                else handleUnify
                                       (searchLocalVars fc rigc defaults trying' depth def top env nty)
                                       (\e => if ambig e
                                                 then throw e
                                                 else tryGroups Nothing nty (hintGroups sd))
                     else throw (CantSolveGoal fc defs [<] top Nothing)
              _ => do logNF "auto" 10 "Next target: " env nty
                      searchLocalVars fc rigc defaults trying' depth def top env nty
  where
    ambig : Error -> Bool
    ambig (AmbiguousSearch _ _ _ _) = True
    ambig _ = False

    -- Take the earliest error message (that's when we look inside pairs,
    -- typically, and it's best to be more precise)
    tryGroups : Maybe Error ->
                NF vars -> List (Bool, List Name) -> Core (Term vars)
    tryGroups (Just err) nty [] = throw err
    tryGroups Nothing nty [] = throw (CantSolveGoal fc !(get Ctxt) [<] top Nothing)
    tryGroups merr nty ((ambigok, g) :: gs)
        = handleUnify
             (do logC "auto" 5
                        (do gn <- traverse getFullName g
                            pure ("Search: Trying " ++ show (length gn) ++
                                           " names " ++ show gn))
                 logNF "auto" 5 "For target" env nty
                 searchNames fc rigc defaults (target :: trying) depth def top env ambigok g nty)
             (\err => if ambig err then throw err
                         else tryGroups (Just $ fromMaybe err merr) nty gs)

-- Declared in Core.Unify.Unify as:
-- search : {vars : _} ->
--          {auto c : Ref Ctxt Defs} ->
--          {auto u : Ref UST UState} ->
--          FC -> RigCount ->
--          (defaults : Bool) -> (depth : Nat) ->
--          (defining : Name) -> (topTy : Term vars) -> Env Term vars ->
--          Core (Term vars)
Core.Unify.Unify.search fc rigc defaults depth def top env
    = do logTermNF "auto" 3 "Initial target: " env top
         log "auto" 3 $ "Running search with defaults " ++ show defaults
         tm <- searchType fc rigc defaults [] depth def
                          True (abstractEnvType fc env top) env
                          top
         logTermNF "auto" 3 "Result" env tm
         pure tm
