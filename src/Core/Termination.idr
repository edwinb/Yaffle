module Core.Termination

import Core.Context
import Core.Context.Log
import Core.Env
import Core.TT
import Core.Evaluate

import Libraries.Data.NameMap
import Libraries.Data.SortedMap
import Data.List
import Data.String
import Data.Vect

%default covering

-- Termination checking follows (more or less)
-- "The size-change principle for program termination" by Lee, Jones and
-- Ben-Amram. https://doi.org/10.1145/360204.360210

-- Check that the names a function refers to are terminating
totRefs : {auto c : Ref Ctxt Defs} ->
          Defs -> List Name -> Core Terminating
totRefs defs [] = pure IsTerminating
totRefs defs (n :: ns)
    = do rest <- totRefs defs ns
         Just d <- lookupCtxtExact n (gamma defs)
              | Nothing => pure rest
         case isTerminating (totality d) of
              IsTerminating => pure rest
              Unchecked => do
                log "totality" 20 $ "Totality unchecked for " ++ show !(toFullNames n)
                pure rest
              _ => case rest of
                          NotTerminating (BadCall ns)
                             => toFullNames $ NotTerminating (BadCall (n :: ns))
                          _ => toFullNames $ NotTerminating (BadCall [n])

totRefsIn : {auto c : Ref Ctxt Defs} ->
            Defs -> Term vars -> Core Terminating
totRefsIn defs ty = totRefs defs (keys (getRefs (Resolved (-1)) ty))

-- Check if all branches end up as constructor arguments, with no other
-- function application, and set 'AllGuarded' if so.
-- This is to check whether a function can be considered a constructor form
-- for the sake of termination checking (and might have other uses...)
export
checkIfGuarded : {auto c : Ref Ctxt Defs} ->
                 FC -> Name -> Core ()
checkIfGuarded fc n
    = do log "totality.termination.guarded" 6 $ "Check if Guarded: " ++ show !(toFullNames n)
         defs <- get Ctxt
         Just (Function _ tm _ _) <- lookupDefExact n (gamma defs)
              | _ => pure ()
         t <- guardedDef !(expand !(nf [<] tm))
         if t then do Just gdef <- lookupCtxtExact n (gamma defs)
                           | Nothing => pure ()
                      g <- allM (checkNotFn defs) (keys (refersTo gdef))
                      when g $ setFlag fc n AllGuarded
              else pure ()
  where
    guardedNF : {vars : _} -> NF vars -> Core Bool
    guardedNF (VDCon{}) = pure True
    guardedNF (VApp _ _ n _ _)
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure False
             pure (AllGuarded `elem` flags gdef)
    guardedNF _ = pure False

    guardedScope : {vars : _} -> (args : _) -> VCaseScope args vars -> Core Bool
    guardedScope [<] sc = guardedNF !(expand !sc)
    guardedScope (sx :< y) sc = guardedScope sx (sc (VErased fc Placeholder))

    guardedAlt : {vars : _} -> VCaseAlt vars -> Core Bool
    guardedAlt (VConCase _ _ _ args sc) = guardedScope _ sc
    guardedAlt (VDelayCase fc ty arg sc)
        = guardedScope [< (top, arg), (top, ty) ] sc
    guardedAlt (VConstCase _ _ sc) = guardedNF !(expand sc)
    guardedAlt (VDefaultCase _ sc) = guardedNF !(expand sc)

    guardedAlts : {vars : _} -> List (VCaseAlt vars) -> Core Bool
    guardedAlts [] = pure True
    guardedAlts (x :: xs)
        = if !(guardedAlt x) then guardedAlts xs else pure False

    guardedDef : {vars : _} -> NF vars -> Core Bool
    guardedDef (VLam fc _ _ _ _ sc)
        = guardedDef !(expand !(sc (VErased fc Placeholder)))
    guardedDef (VCase fc c _ _ alts)
        = guardedAlts alts
    guardedDef nf = guardedNF nf

    checkNotFn : Defs -> Name -> Core Bool
    checkNotFn defs n
        = do Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure False
             case definition gdef of
                  DCon _ _ _ => pure True
                  _ => pure (multiplicity gdef == erased
                              || (AllGuarded `elem` flags gdef))

-- Equal for the purposes of size change means, ignoring as patterns, all
-- non-metavariable positions are equal
scEq : Term vars -> Term vars -> Bool
scEq (Local _ idx _) (Local _ idx' _) = idx == idx'
scEq (Ref _ _ n) (Ref _ _ n') = n == n'
scEq (Meta _ _ i args) _ = True
scEq _ (Meta _ _ i args) = True
scEq (Bind _ _ b sc) (Bind _ _ b' sc') = False -- not checkable
scEq (App _ f _ a) (App _ f' _ a') = scEq f f' && scEq a a'
scEq (As _ _ a p) p' = scEq p p'
scEq p (As _ _ a p') = scEq p p'
scEq (Case _ _ sc ty alts) (Case _ _ sc' ty' alts') = False -- not checkable
scEq (TDelayed _ _ t) (TDelayed _ _ t') = scEq t t'
scEq (TDelay _ _ t x) (TDelay _ _ t' x') = scEq t t' && scEq x x'
scEq (TForce _ _ t) (TForce _ _ t') = scEq t t'
scEq (PrimVal _ c) (PrimVal _ c') = c == c'
scEq (Erased _ _) (Erased _ _) = True
scEq (Unmatched _ _) (Unmatched _ _) = True
scEq (TType _ _) (TType _ _) = True
scEq _ _ = False -- other cases not checkable

data Guardedness = Toplevel | Unguarded | Guarded | InDelay

Show Guardedness where
  show Toplevel = "Toplevel"
  show Unguarded = "Unguarded"
  show Guarded = "Guarded"
  show InDelay = "InDelay"

-- Remove all force and delay annotations which are nothing to do with
-- coinduction meaning that all Delays left guard coinductive calls.
delazy : Term vars -> Term vars
delazy (TDelayed fc r tm)
    = let tm' = delazy tm in
          case r of
               LInf => TDelayed fc r tm'
               _ => tm'
delazy (TDelay fc r ty tm)
    = let ty' = delazy ty
          tm' = delazy tm in
          case r of
               LInf => TDelay fc r ty' tm'
               _ => tm'
delazy (TForce fc r t)
    = case r of
           LInf => TForce fc r (delazy t)
           _ => delazy t
delazy (Meta fc n i args) = Meta fc n i (map (\ (c, t) => (c, delazy t)) args)
delazy (Bind fc x b sc)
    = Bind fc x (map (delazy) b) (delazy sc)
delazy (App fc f c a) = App fc (delazy f) c (delazy a)
delazy (As fc s a p) = As fc s a (delazy p)
delazy (Case fc c sc ty alts)
    = Case fc c (delazy sc) (delazy ty) (map delazyAlt alts)
  where
    delazyScope : forall vars . CaseScope vars -> CaseScope vars
    delazyScope (RHS tm) = RHS (delazy tm)
    delazyScope (Arg c x sc) = Arg c x (delazyScope sc)

    delazyAlt : forall vars . CaseAlt vars -> CaseAlt vars
    delazyAlt (ConCase fc n t sc) = ConCase fc n t (delazyScope sc)
    delazyAlt (DelayCase fc ty arg tm) = DelayCase fc ty arg (delazy tm)
    delazyAlt (ConstCase fc c tm) = ConstCase fc c (delazy tm)
    delazyAlt (DefaultCase fc tm) = DefaultCase fc (delazy tm)

delazy (PrimOp fc op args) = PrimOp fc op (map delazy args)
delazy tm = tm

-- Return whether first argument is structurally smaller than the second.
smaller : Bool -> -- Have we gone under a constructor yet?
          Maybe (Term vars) -> -- Asserted bigger thing
          Term vars -> -- Term we're checking
          Term vars -> -- Argument it might be smaller than
          Bool

assertedSmaller : Maybe (Term vars) -> Term vars -> Bool

smallerArg : Bool ->
             Maybe (Term vars) -> Term vars -> Term vars -> Bool
smallerArg inc big (As _ _ _ s) tm = smallerArg inc big s tm
smallerArg inc big s tm
      -- If we hit a pattern that is equal to a thing we've asserted_smaller,
      -- the argument must be smaller
    = assertedSmaller big tm ||
              case getFnArgs tm of
                   (Ref _ (DataCon t a) cn, args)
                       => any (smaller True big s) args
                   _ => case s of
                             App _ f _ _ => smaller inc big f tm
                                          -- Higher order recursive argument
                             _ => False

smaller inc big _ (Erased _ _) = False -- Never smaller than an erased thing!
-- for an as pattern, it's smaller if it's smaller than the pattern
-- or if we've gone under a constructor and it's smaller than the variable
smaller True big s (As _ _ a t)
    = smaller True big s a ||
      smaller True big s t
smaller True big s t
    = scEq s t || smallerArg True big s t
smaller inc big s t = smallerArg inc big s t

assertedSmaller (Just b) a = scEq b a
assertedSmaller _ _ = False

findSC : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         Guardedness ->
         List (Nat, Term vars) -> -- LHS args and their position
         Term vars -> -- definition
         Core (List SCCall)

-- Expand the size change argument list with 'Nothing' to match the given
-- arity (i.e. the arity of the function we're calling) to ensure that
-- it's noted that we don't know the size change relationship with the
-- extra arguments.
expandToArity : Nat -> List (Maybe (Nat, SizeChange)) ->
                List (Maybe (Nat, SizeChange))
expandToArity Z xs = xs
expandToArity (S k) (x :: xs) = x :: expandToArity k xs
expandToArity (S k) [] = Nothing :: expandToArity k []

-- if the argument is an 'assert_smaller', return the thing it's smaller than
asserted : Name -> Term vars -> Maybe (Term vars)
asserted aSmaller tm
     = case getFnArgs tm of
            (Ref _ nt fn, [_, _, b, _])
                 => if fn == aSmaller
                       then Just b
                       else Nothing
            _ => Nothing

-- Calculate the size change for the given argument.
-- i.e., return the size relationship of the given argument with an entry
-- in 'pats'; the position in 'pats' and the size change.
-- Nothing if there is no relation with any of them.
mkChange : Name ->
           (pats : List (Nat, Term vars)) ->
           (arg : Term vars) ->
           Maybe (Nat, SizeChange)
mkChange aSmaller [] arg = Nothing
-- mkChange defs aSmaller ((i, As _ _ p parg) :: pats) arg
--     = mkChange defs aSmaller ((i, p) :: (i, parg) :: pats) arg
mkChange aSmaller ((i, parg) :: pats) arg
    = cond [(scEq arg parg, Just (i, Same)),
            (smaller False (asserted aSmaller arg) arg parg, Just (i, Smaller))]
        (mkChange aSmaller pats arg)

findSCcall : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             Guardedness ->
             List (Nat, Term vars) ->
             FC -> Name -> Nat -> List (Term vars) ->
             Core (List SCCall)
findSCcall g pats fc fn_in arity args
        -- Under 'assert_total' we assume that all calls are fine, so leave
        -- the size change list empty
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact fn_in (gamma defs)
                | Nothing => undefinedName fc fn_in
           let fn = fullname gdef
           log "totality.termination.sizechange" 10 $ "Looking under " ++ show !(toFullNames fn)
           aSmaller <- resolved (gamma defs) (NS builtinNS (UN $ Basic "assert_smaller"))
           if fn == NS builtinNS (UN $ Basic "assert_total")
              then pure []
              else
               do scs <- traverse (findSC g pats) args
                  pure ([MkSCCall fn
                           (expandToArity arity
                                (map (mkChange aSmaller pats) args))]
                           ++ concat scs)

replaceInArgs : Var vars -> Term vars ->
                List (Nat, Term vars) -> List (Nat, Term vars)
replaceInArgs v tm = map (\ (n, arg) => (n, substVar v tm arg))

findSCscope : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         Guardedness ->
         List (Nat, Term vars) -> -- LHS args and their position
         Maybe (Var vars) -> -- variable we're splitting on (if it is a variable)
         FC -> Term vars -> CaseScope vars -> -- case alternative
         Core (List SCCall)
findSCscope g args var fc pat (RHS tm)
    = findSC g (maybe args (\v => replaceInArgs v pat args) var) tm
findSCscope g args var fc pat (Arg c x sc)
    = let args' = map (\ (i, tm) => (i, weaken tm)) args
          var' = map weaken var
          pat' = App fc (weaken pat) c (Local fc 0 First) in
        findSCscope g args' var' fc pat' sc

findSCalt : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         Guardedness ->
         List (Nat, Term vars) -> -- LHS args and their position
         Maybe (Var vars) -> -- variable we're splitting on (if it is a variable)
         CaseAlt vars -> -- case alternative
         Core (List SCCall)
findSCalt g args var (ConCase fc n t sc)
    = findSCscope g args var fc (Ref fc (DataCon t (arity sc)) n) sc
  where
    arity : CaseScope vs -> Nat
    arity (RHS _) = 0
    arity (Arg _ _ sc) = S (arity sc)
findSCalt g args var (DelayCase fc ty arg tm)
    = let s = mkSizeOf [< arg, ty]
          args' = map (\ (i, tm) => (i, weakenNs s tm)) args
          var' = map (weakenNs s) var
          pat = TDelay fc LUnknown (Local fc _ (Later First))
                                   (Local fc _ First) in
      findSC g (maybe args' (\v => replaceInArgs v pat args') var') tm
findSCalt g args var (ConstCase fc c tm)
    = findSC g (maybe args (\v => replaceInArgs v (PrimVal fc c) args) var) tm
findSCalt g args var (DefaultCase fc tm) = findSC g args tm

findSC {vars} g args (Bind fc n b sc)
       = pure $
            !(findSCbinder b) ++
            !(findSC g (map (\ (p, tm) => (p, weaken tm)) args) sc)
    where
      findSCbinder : Binder (Term vars) -> Core (List SCCall)
      findSCbinder (Let _ c val ty) = findSC g args val
      findSCbinder b = pure [] -- only types, no need to look
-- If we're Guarded and find a Delay, continue with the argument as InDelay
findSC Guarded pats (TDelay _ _ _ tm)
    = findSC InDelay pats tm
findSC g pats (TDelay _ _ _ tm)
    = findSC g pats tm
findSC g args (Case fc c (Local lfc idx p) scTy alts)
    = do altCalls <- traverse (findSCalt g args (Just (MkVar p))) alts
         pure (concat altCalls)
findSC g args (Case fc c sc scTy alts)
    = do altCalls <- traverse (findSCalt g args Nothing) alts
         scCalls <- findSC Unguarded args sc
         pure (scCalls ++ concat altCalls)
findSC g pats tm
    = do let (fn, args) = getFnArgs tm
         fn' <- conIfGuarded fn -- pretend it's a data constructor if
                                  -- it has the AllGuarded flag
         case (g, fn', args) of
    -- If we're InDelay and find a constructor (or a function call which is
    -- guaranteed to return a constructor; AllGuarded set), continue as InDelay
           (InDelay, Ref fc (DataCon _ _) cn, args) =>
               do scs <- traverse (findSC InDelay pats) args
                  pure (concat scs)
           -- If we're InDelay otherwise, just check the arguments, the
           -- function call is okay
           (InDelay, _, args) =>
               do scs <- traverse (findSC Unguarded pats) args
                  pure (concat scs)
           (Guarded, Ref fc (DataCon _ _) cn, args) =>
               do scs <- traverse (findSC Guarded pats) args
                  pure (concat scs)
           (Toplevel, Ref fc (DataCon _ _) cn, args) =>
               do scs <- traverse (findSC Guarded pats) args
                  pure (concat scs)
           (_, Ref fc Func fn, args) =>
               do logC "totality" 50 $
                     pure $ "Looking up type of " ++ show !(toFullNames fn)
                  defs <- get Ctxt
                  Just ty <- lookupTyExact fn (gamma defs)
                       | Nothing => do
                            log "totality" 50 $ "Lookup failed"
                            findSCcall Unguarded pats fc fn 0 args
                  arity <- getArity [<] ty
                  findSCcall Unguarded pats fc fn arity args
           (_, f, args) =>
               do scs <- traverse (findSC Unguarded pats) args
                  pure (concat scs)
      where
        conIfGuarded : Term vars -> Core (Term vars)
        conIfGuarded (Ref fc Func n)
            = do defs <- get Ctxt
                 Just gdef <- lookupCtxtExact n (gamma defs)
                      | Nothing => pure $ Ref fc Func n
                 if AllGuarded `elem` flags gdef
                    then pure $ Ref fc (DataCon 0 0) n
                    else pure $ Ref fc Func n
        conIfGuarded tm = pure tm

findSCTop : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            Nat -> List (Nat, Term vars) -> Term vars -> Core (List SCCall)
findSCTop i args (Bind fc x (Lam lfc c p ty) sc)
    = findSCTop (1 + i) ((i, Local lfc _ First) :: wkn args) sc
  where
    wkn : List (Nat, Term vars) -> List (Nat, Term (vars :< n))
    wkn [] = []
    wkn ((i, tm) :: args) = (i, weaken tm) :: wkn args
findSCTop i args def = findSC Toplevel args def

findCalls : {auto c : Ref Ctxt Defs} ->
            ClosedTerm -> Core (List SCCall)
findCalls tm = findSCTop 0 [] (delazy tm)

getSC : {auto c : Ref Ctxt Defs} ->
        Defs -> Def -> Core (List SCCall)
getSC defs (Function _ tm _ _)
   = do sc <- findCalls tm
        pure $ nub sc
getSC defs _ = pure []

export
calculateSizeChange : {auto c : Ref Ctxt Defs} ->
                      FC -> Name -> Core (List SCCall)
calculateSizeChange loc n
    = do log "totality.termination.sizechange" 5 $ "Calculating Size Change: " ++ show !(toFullNames n)
         defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         getSC defs (definition def)

Arg : Type
Arg = Int

data APos : Type where

firstArg : Arg
firstArg = 0

nextArg : Arg -> Arg
nextArg x = x + 1

initArgs : {auto a : Ref APos Arg} ->
           Nat -> Core (List (Maybe (Arg, SizeChange)))
initArgs Z = pure []
initArgs (S k)
    = do arg <- get APos
         put APos (nextArg arg)
         args' <- initArgs k
         pure (Just (arg, Same) :: args')

data Explored : Type where

-- Cached results of exploring the size change graph, so that if we visit a
-- node again, we don't have to re-explore the whole thing
SizeChanges : Type
SizeChanges = SortedMap (Name, List (Maybe Arg)) Terminating

-- Traverse the size change graph. When we reach a point we've seen before,
-- at least one of the arguments must have got smaller, otherwise it's
-- potentially non-terminating
checkSC : {auto a : Ref APos Arg} ->
          {auto c : Ref Ctxt Defs} ->
          {auto e : Ref Explored SizeChanges} ->
          Defs ->
          Name -> -- function we're checking
          List (Maybe (Arg, SizeChange)) -> -- functions arguments and change
          List (Name, List (Maybe Arg)) -> -- calls we've seen so far
          Core Terminating
checkSC defs f args path
   = do exp <- get Explored
        log "totality.termination.sizechange" 7 $ "Checking Size Change Graph: " ++ show !(toFullNames f)
        let pos = (f, map (map Builtin.fst) args)
        case lookup pos exp of
             Just done => pure done -- already explored this bit of tree
             Nothing =>
                if pos `elem` path
                   then do log "totality.termination.sizechange.inPath" 8 $ "Checking arguments: " ++ show !(toFullNames f)
                           res <- toFullNames $ checkDesc (mapMaybe (map Builtin.snd) args) path
                           put Explored (insert pos res exp)
                           pure res
                   else case !(lookupCtxtExact f (gamma defs)) of
                             Nothing => do log "totality.termination.sizechange.isTerminating" 8 $ "Size Change Graph is Terminating for: " ++ show !(toFullNames f)
                                           pure IsTerminating
                             Just def => do log "totality.termination.sizechange.needsChecking" 8 $ "Size Change Graph needs traversing: " ++ show !(toFullNames f)
                                            continue (sizeChange def) (pos :: path)
  where
    -- Look for something descending in the list of size changes
    checkDesc : List SizeChange -> List (Name, List (Maybe Arg)) -> Terminating
    checkDesc [] path = NotTerminating (RecPath (reverse (map fst path)))
    checkDesc (Smaller :: _) _ = IsTerminating
    checkDesc (_ :: xs) path = checkDesc xs path

    getPos : forall a . List a -> Nat -> Maybe a
    getPos [] _ = Nothing
    getPos (x :: xs) Z = Just x
    getPos (x :: xs) (S k) = getPos xs k

    updateArg : SizeChange -> Maybe (Arg, SizeChange) -> Maybe (Arg, SizeChange)
    updateArg c Nothing = Nothing
    updateArg c arg@(Just (i, Unknown)) = arg
    updateArg Unknown (Just (i, _)) = Just (i, Unknown)
    updateArg c (Just (i, Same)) = Just (i, c)
    updateArg c arg = arg

    mkArgs : List (Maybe (Nat, SizeChange)) -> List (Maybe (Arg, SizeChange))
    mkArgs [] = []
    mkArgs (Nothing :: xs) = Nothing :: mkArgs xs
    mkArgs (Just (pos, c) :: xs)
        = case getPos args pos of
               Nothing => Nothing :: mkArgs xs
               Just arg => updateArg c arg :: mkArgs xs

    checkCall : List (Name, List (Maybe Arg)) -> SCCall -> Core Terminating
    checkCall path sc
        = do Just gdef <- lookupCtxtExact (fnCall sc) (gamma defs)
                  | Nothing => pure IsTerminating -- nothing to check
             let Unchecked = isTerminating (totality gdef)
                  | IsTerminating => pure IsTerminating
                  | _ => pure (NotTerminating (BadCall [fnCall sc]))
             log "totality.termination.sizechange.checkCall" 8 $
                "CheckCall Size Change Graph: " ++ show !(toFullNames (fnCall sc))
             term <- checkSC defs (fnCall sc) (mkArgs (fnArgs sc)) path
             let inpath = fnCall sc `elem` map fst path
             if not inpath
                then case term of
                       NotTerminating (RecPath _) =>
                          -- might have lost information while assuming this
                          -- was mutually recursive, so start again with new
                          -- arguments (that is, where we'd start if the
                          -- function was the top level thing we were checking)
                          do log "totality.termination.sizechange.checkCall.inPathNot.restart" 9 $ "ReChecking Size Change Graph: " ++ show !(toFullNames (fnCall sc))
                             args' <- initArgs (length (fnArgs sc))
                             t <- checkSC defs (fnCall sc) args' path
                             setTerminating emptyFC (fnCall sc) t
                             pure t
                       t => do log "totality.termination.sizechange.checkCall.inPathNot.return" 9 $ "Have result: " ++ show !(toFullNames (fnCall sc))
                               pure t
                else do log "totality.termination.sizechange.checkCall.inPath" 9 $ "Have Result: " ++ show !(toFullNames (fnCall sc))
                        pure term

    getWorst : Terminating -> List Terminating -> Terminating
    getWorst term [] = term
    getWorst term (IsTerminating :: xs) = getWorst term xs
    getWorst term (Unchecked :: xs) = getWorst Unchecked xs
    getWorst term (bad :: xs) = bad

    continue : List SCCall -> List (Name, List (Maybe Arg)) -> Core Terminating
    continue scs path
        = do allTerm <- traverse (checkCall path) scs
             pure (getWorst IsTerminating allTerm)

calcTerminating : {auto c : Ref Ctxt Defs} ->
                  FC -> Name -> Core Terminating
calcTerminating loc n
    = do defs <- get Ctxt
         log "totality.termination.calc" 7 $ "Calculating termination: " ++ show !(toFullNames n)
         case !(lookupCtxtExact n (gamma defs)) of
              Nothing => undefinedName loc n
              Just def =>
                case !(totRefs defs (keys (refersTo def))) of
                     IsTerminating =>
                        do let ty = type def
                           a <- newRef APos firstArg
                           args <- initArgs !(getArity [<] ty)
                           e <- newRef Explored empty
                           checkSC defs n args []
                     bad => pure bad

-- Check whether a function is terminating, and record in the context
export
checkTerminating : {auto c : Ref Ctxt Defs} ->
                   FC -> Name -> Core Terminating
checkTerminating loc n
    = do tot <- getTotality loc n
         log "totality.termination" 6 $ "Checking termination: " ++ show !(toFullNames n)
         case isTerminating tot of
              Unchecked =>
                 do tot' <- calcTerminating loc n
                    setTerminating loc n tot'
                    pure tot'
              t => pure t

nameIn : {auto c : Ref Ctxt Defs} ->
         List Name -> NF [<] -> Core Bool
nameIn tyns (VBind fc x b sc)
    = if !(nameIn tyns !(expand (binderType b)))
         then pure True
         else do sc' <- sc (vRef fc Bound (MN ("NAMEIN_" ++ show x) 0))
                 nameIn tyns !(expand sc')
nameIn tyns (VApp _ nt n args _)
    = anyM (nameIn tyns) (cast !(traverseSnocList spineVal args))
nameIn tyns (VTCon _ n _ args)
    = if n `elem` tyns
         then pure True
         else do args' <- traverseSnocList spineVal args
                 anyM (nameIn tyns) (cast args')
nameIn tyns (VDCon _ n _ _ args)
    = anyM (nameIn tyns)
           (cast !(traverseSnocList spineVal args))
nameIn tyns _ = pure False

-- Check an argument type doesn't contain a negative occurrence of any of
-- the given type names
posArg  : {auto c : Ref Ctxt Defs} ->
          List Name -> NF [<] -> Core Terminating

posArgs : {auto c : Ref Ctxt Defs} ->
          List Name -> SnocList (Glued [<]) -> Core Terminating
posArgs tyn [<] = pure IsTerminating
posArgs tyn (xs :< x)
  = do xNF <- expand x
       logNF "totality.positivity" 50 "Checking parameter for positivity" [<] xNF
       IsTerminating <- posArg tyn xNF
          | err => pure err
       posArgs tyn xs

-- a tyn can only appear in the parameter positions of
-- tc; report positivity failure if it appears anywhere else
posArg tyns nf@(VTCon loc tc _ args) =
  do logNF "totality.positivity" 50 "Found a type constructor" [<] nf
     defs <- get Ctxt
     testargs <- case !(lookupDefExact tc (gamma defs)) of
                    Just (TCon ti _) => do
                         let params = paramPos ti
                         log "totality.positivity" 50 $
                           unwords [show tc, "has", show (length params), "parameters"]
                         pure $ splitParams 0 params (map spineArg args)
                    _ => throw (GenericMsg loc (show tc ++ " not a data type"))
     let (params, indices) = testargs
     False <- anyM (nameIn tyns) (cast !(traverseSnocList expand indices))
       | True => pure (NotTerminating NotStrictlyPositive)
     posArgs tyns params
  where
    splitParams : Nat -> List Nat -> SnocList (Glued [<]) ->
        ( SnocList (Glued [<]) -- parameters (to be checked for strict positivity)
        , SnocList (Glued [<]) -- indices    (to be checked for no mention at all)
        )
    splitParams i ps [<] = ([<], [<])
    splitParams i ps (xs :< x)
        = if i `elem` ps
             then mapFst (:< x) (splitParams (S i) ps xs)
             else mapSnd (:< x) (splitParams (S i) ps xs)
-- a tyn can not appear as part of ty
posArg tyns nf@(VBind fc x (Pi _ _ e ty) sc)
  = do logNF "totality.positivity" 50 "Found a Pi-type" [<] nf
       if !(nameIn tyns !(expand ty))
         then pure (NotTerminating NotStrictlyPositive)
         else do sc' <- sc (vRef fc Bound (MN ("POSCHECK_" ++ show x) 1))
                 posArg tyns !(expand sc')
posArg tyns nf@(VApp _ _ _ args _)
    = do logNF "totality.positivity" 50 "Found an application" [<] nf
         args <- traverseSnocList spineVal args
         pure $ if !(anyM (nameIn tyns) (cast args))
           then NotTerminating NotStrictlyPositive
           else IsTerminating
posArg tyn nf
  = do logNF "totality.positivity" 50 "Reached the catchall" [<] nf
       pure IsTerminating

checkPosArgs : {auto c : Ref Ctxt Defs} ->
               List Name -> NF [<] -> Core Terminating
checkPosArgs tyns (VBind fc x (Pi _ _ e ty) sc)
    = case !(posArg tyns !(expand ty)) of
           IsTerminating =>
               do let nm = vRef fc Bound (MN ("POSCHECK_" ++ show x) 0)
                  checkPosArgs tyns !(expand !(sc nm))
           bad => pure bad
checkPosArgs tyns nf
  = do logNF "totality.positivity" 50 "Giving up on non-Pi type" [<] nf
       pure IsTerminating

checkCon : {auto c : Ref Ctxt Defs} ->
           List Name -> Name -> Core Terminating
checkCon tyns cn
    = do defs <- get Ctxt
         case !(lookupTyExact cn (gamma defs)) of
           Nothing => do log "totality.positivity" 20 $
                           "Couldn't find constructor " ++ show cn
                         pure Unchecked
           Just ty =>
             case !(totRefsIn defs ty) of
                IsTerminating =>
                  do tyNF <- nf [<] ty
                     logNF "totality.positivity" 20 "Checking the type " [<] tyNF
                     checkPosArgs tyns !(expand tyNF)
                bad => pure bad

checkData : {auto c : Ref Ctxt Defs} ->
            List Name -> List Name -> Core Terminating
checkData tyns [] = pure IsTerminating
checkData tyns (c :: cs)
    = do log "totality.positivity" 40 $
           "Checking positivity of constructor " ++ show c
         case !(checkCon tyns c) of
           IsTerminating => checkData tyns cs
           bad => pure bad

-- Calculate whether a type satisfies the strict positivity condition, and
-- return whether it's terminating, along with its data constructors
calcPositive : {auto c : Ref Ctxt Defs} ->
               FC -> Name -> Core (Terminating, List Name)
calcPositive loc n
    = do defs <- get Ctxt
         log "totality.positivity" 6 $ "Calculating positivity: " ++ show !(toFullNames n)
         case !(lookupDefTyExact n (gamma defs)) of
              Just (TCon ti _, ty) =>
                let tns = mutWith ti
                    dcons = datacons ti in
                  case !(totRefsIn defs ty) of
                       IsTerminating =>
                            do log "totality.positivity" 30 $
                                 "Now checking constructors of " ++ show !(toFullNames n)
                               t <- checkData (n :: tns) dcons
                               pure (t , dcons)
                       bad => pure (bad, dcons)
              Just _ => throw (GenericMsg loc (show n ++ " not a data type"))
              Nothing => undefinedName loc n

-- Check whether a data type satisfies the strict positivity condition, and
-- record in the context
export
checkPositive : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Core Terminating
checkPositive loc n_in
    = do n <- toResolvedNames n_in
         tot <- getTotality loc n
         log "totality.positivity" 6 $ "Checking positivity: " ++ show !(toFullNames n)
         case isTerminating tot of
              Unchecked =>
                  do (tot', cons) <- calcPositive loc n
                     setTerminating loc n tot'
                     traverse_ (\c => setTerminating loc c tot') cons
                     pure tot'
              t => pure t

-- Check and record totality of the given name; positivity if it's a data
-- type, termination if it's a function
export
checkTotal : {auto c : Ref Ctxt Defs} ->
             FC -> Name -> Core Terminating
checkTotal loc n_in
    = do defs <- get Ctxt
         let Just nidx = getNameID n_in (gamma defs)
             | Nothing => undefinedName loc n_in
         let n = Resolved nidx
         tot <- getTotality loc n
         log "totality" 5 $ "Checking totality: " ++ show !(toFullNames n)
         defs <- get Ctxt
         case isTerminating tot of
              Unchecked => do
                  mgdef <- lookupCtxtExact n (gamma defs)
                  case definition <$> mgdef of
                       Just (TCon{})
                           => checkPositive loc n
                       _ => do whenJust (refersToM =<< mgdef) $ \ refs =>
                                 log "totality" 5 $ "  Mutually defined with:"
                                                 ++ show !(traverse toFullNames (keys refs))
                               checkTerminating loc n
              t => pure t
