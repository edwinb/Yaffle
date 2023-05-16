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
         tmnf <- nf [<] tm
         -- Just work from 'Glued', don't do any actual normalisation
         t <- guardedDef tmnf
         log "totality.termination.guarded" 6 (show t)
         if t then do Just gdef <- lookupCtxtExact n (gamma defs)
                           | Nothing => pure ()
                      g <- allM (checkNotFn defs) (keys (refersTo gdef))
                      log "totality.termination.guarded" 6
                            $ "Refers to " ++ show !(toFullNames (keys (refersTo gdef)))
                      when g $ setFlag fc n AllGuarded
              else pure ()
  where
    guardedNF : {vars : _} -> Glued vars -> Core Bool
    guardedNF (VDCon{}) = pure True
    guardedNF (VApp _ _ n _ _)
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure False
             pure (AllGuarded `elem` flags gdef)
    guardedNF _ = pure False

    guardedScope : {vars : _} -> (args : _) -> VCaseScope args vars -> Core Bool
    guardedScope [<] sc = guardedNF (snd !sc)
    guardedScope (sx :< y) sc = guardedScope sx (sc (pure (VErased fc Placeholder)))

    guardedAlt : {vars : _} -> VCaseAlt vars -> Core Bool
    guardedAlt (VConCase _ _ _ args sc) = guardedScope _ sc
    guardedAlt (VDelayCase fc ty arg sc)
        = guardedScope [< (top, arg), (top, ty) ] sc
    guardedAlt (VConstCase _ _ sc) = guardedNF sc
    guardedAlt (VDefaultCase _ sc) = guardedNF sc

    guardedAlts : {vars : _} -> List (VCaseAlt vars) -> Core Bool
    guardedAlts [] = pure True
    guardedAlts (x :: xs)
        = if !(guardedAlt x) then guardedAlts xs else pure False

    guardedDef : {vars : _} ->  Glued vars -> Core Bool
    guardedDef (VLam fc _ _ _ _ sc)
        = guardedDef !(sc (pure (VErased fc Placeholder)))
    guardedDef (VCase fc ct c _ _ alts)
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

-- Drop any non-inf top level laziness annotations
dropLazy : Value f vars -> Core (Glued vars)
dropLazy val@(VDelayed _ r t)
    = case r of
           LInf => pure (asGlued val)
           _ => pure t
dropLazy val@(VDelay _ r t v)
    = case r of
           LInf => pure (asGlued val)
           _ => pure v
dropLazy val@(VForce fc r v sp)
    = case r of
           LInf => pure (asGlued val)
           _ => applyAll fc v (cast (map snd sp))
dropLazy val = pure (asGlued val)

-- Equal for the purposes of size change means, ignoring as patterns, all
-- non-metavariable positions are equal
scEq : Value f vars -> Value f' vars -> Core Bool

scEqSpine : Spine vars -> Spine vars -> Core Bool
scEqSpine [<] [<] = pure True
scEqSpine (sp :< (_, _, x)) (sp' :< (_, _, y))
    = do x' <- x
         y' <- y
         if !(scEq x' y')
            then scEqSpine sp sp'
            else pure False
scEqSpine _ _ = pure False

-- Approximate equality between values. We don't go under binders - we're
-- only checking for size change equality so expect to just see type and
-- data constructors
-- TODO: size change for pattern matching on types
scEq' : Value f vars -> Value f' vars -> Core Bool
scEq' (VApp _ _ n sp _) (VApp _ _ n' sp' _)
    = if n == n'
         then scEqSpine sp sp'
         else pure False
-- Should never see this since we always call with vars = [<], but it is
-- technically possible
scEq' (VLocal _ idx _ sp) (VLocal _ idx' _ sp')
    = if idx == idx'
         then scEqSpine sp sp'
         else pure False
scEq' (VDCon _ _ t a sp) (VDCon _ _ t' a' sp')
    = if t == t'
         then scEqSpine sp sp'
         else pure False
scEq' (VTCon _ n a sp) (VTCon _ n' a' sp')
    = if n == n'
         then scEqSpine sp sp'
         else pure False
scEq' (VMeta{}) _ = pure True
scEq' _ (VMeta{}) = pure True
scEq' (VAs _ _ a p) p' = scEq p p'
scEq' p (VAs _ _ a p') = scEq p p'
scEq' (VDelayed _ _ t) (VDelayed _ _ t') = scEq t t'
scEq' (VDelay _ _ t x) (VDelay _ _ t' x')
     = if !(scEq t t') then scEq x x'
          else pure False
scEq' (VForce _ _ t [<]) (VForce _ _ t' [<]) = scEq t t'
scEq' (VPrimVal _ c) (VPrimVal _ c') = pure $ c == c'
scEq' (VErased _ _) (VErased _ _) = pure True
scEq' (VUnmatched _ _) (VUnmatched _ _) = pure True
scEq' (VType _ _) (VType _ _) = pure True
scEq' _ _ = pure False -- other cases not checkable

scEq x y = scEq' !(dropLazy x) !(dropLazy y)

data Guardedness = Toplevel | Unguarded | Guarded | InDelay

Show Guardedness where
  show Toplevel = "Toplevel"
  show Unguarded = "Unguarded"
  show Guarded = "Guarded"
  show InDelay = "InDelay"

assertedSmaller : Maybe (Glued [<]) -> Glued [<] -> Core Bool
assertedSmaller (Just b) a = scEq b a
assertedSmaller _ _ = pure False

-- Return whether first argument is structurally smaller than the second.
smaller : Bool -> -- Have we gone under a constructor yet?
          Maybe (Glued [<]) -> -- Asserted bigger thing
          Glued [<] -> -- Term we're checking
          Glued [<] -> -- Argument it might be smaller than
          Core Bool

smallerArg : Bool ->
             Maybe (Glued [<]) -> Glued [<] -> Glued [<] -> Core Bool
smallerArg inc big (VAs _ _ _ s) tm = smallerArg inc big s tm
smallerArg inc big s tm
      -- If we hit a pattern that is equal to a thing we've asserted_smaller,
      -- the argument must be smaller
    = if !(assertedSmaller big tm)
         then pure True
         else case tm of
                   VDCon _ _ _ _ sp
                       => anyM (smaller True big s)
                                (cast !(traverseSnocList (snd . snd) sp))
                   _ => case s of
                             VApp fc nt n sp@(_ :< _) _ =>
                                -- Higher order recursive argument
                                  smaller inc big
                                      (VApp fc nt n [<] (pure Nothing))
                                      tm
                             _ => pure False

smaller inc big _ (VErased _ _) = pure False -- Never smaller than an erased thing!
-- for an as pattern, it's smaller if it's smaller than the pattern
-- or if we've gone under a constructor and it's smaller than the variable
smaller True big s (VAs _ _ a t)
    = if !(smaller True big s a)
         then pure True
         else smaller True big s t
smaller True big s t
    = if !(scEq s t)
         then pure True
         else smallerArg True big s t
smaller inc big s t = smallerArg inc big s t

data SCVar : Type where

mkvar : Int -> Value f [<]
mkvar i = VApp EmptyFC Bound (MN "scv" i) [<] (pure Nothing)

nextVar : {auto c : Ref SCVar Int} -> Core (Value f [<])
nextVar
    = do v <- get SCVar
         put SCVar (v + 1)
         pure (mkvar v)

ForcedEqs : Type
ForcedEqs = List (Glued [<], Glued [<])

findSC : {auto c : Ref Ctxt Defs} ->
         {auto v : Ref SCVar Int} ->
         Guardedness ->
         ForcedEqs ->
         List (Nat, Glued [<]) -> -- LHS args and their position
         Glued [<] -> -- definition. No expanding to NF, we want to check
                      -- the program as written (plus tcinlines)
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

findVar : Int -> List (Glued vars, Glued vars) -> Maybe (Glued vars)
findVar i [] = Nothing
findVar i ((VApp _ Bound (MN _ i') _ _, tm) :: eqs)
    = if i == i' then Just tm else findVar i eqs
findVar i (_ :: eqs) = findVar i eqs

canonicalise : List (Glued vars, Glued vars) -> Glued vars -> Core (Glued vars)
canonicalise eqs tm@(VApp _ Bound (MN _ i) _ _)
    = case findVar i eqs of
           Nothing => pure tm
           Just val => canonicalise eqs val
canonicalise eqs (VDCon fc cn t a sp)
    = pure $ VDCon fc cn t a !(canonSp sp)
  where
    canonSp : Spine vars -> Core (Spine vars)
    canonSp [<] = pure [<]
    canonSp (rest :< (fc, c, arg))
        = do rest' <- canonSp rest
             pure (rest' :< (fc, c, canonicalise eqs !arg))
-- for matching on types, convert to the form the case tree builder uses
canonicalise eqs (VPrimVal fc (PrT c))
    = pure $ (VTCon fc (UN (Basic $ show c)) 0 [<])
canonicalise eqs (VType fc _)
    = pure $ (VTCon fc (UN (Basic "Type")) 0 [<])
canonicalise eqs val = pure val

-- if the argument is an 'assert_smaller', return the thing it's smaller than
asserted : ForcedEqs -> Name -> Glued [<] -> Core (Maybe (Glued [<]))
asserted eqs aSmaller (VApp _ nt fn [<_, _, (_, _, b), _] _)
     = if fn == aSmaller
          then Just <$> canonicalise eqs !b
          else pure Nothing
asserted _ _ _ = pure Nothing

-- Calculate the size change for the given argument.
-- i.e., return the size relationship of the given argument with an entry
-- in 'pats'; the position in 'pats' and the size change.
-- Nothing if there is no relation with any of them.
mkChange : {auto c : Ref Ctxt Defs} ->
           ForcedEqs ->
           Name ->
           (pats : List (Nat, Glued [<])) ->
           (arg : Glued [<]) ->
           Core (Maybe (Nat, SizeChange))
mkChange eqs aSmaller [] arg = pure Nothing
mkChange eqs aSmaller ((i, parg) :: pats) arg
    = if !(scEq arg parg)
         then pure (Just (i, Same))
         else do s <- smaller False !(asserted eqs aSmaller arg) arg parg
                 if s then pure (Just (i, Smaller))
                      else mkChange eqs aSmaller pats arg

findSCcall : {auto c : Ref Ctxt Defs} ->
             {auto v : Ref SCVar Int} ->
             Guardedness ->
             ForcedEqs ->
             List (Nat, Glued [<]) ->
             FC -> Name -> Nat -> List (Glued [<]) ->
             Core (List SCCall)
findSCcall g eqs pats fc fn_in arity args
        -- Under 'assert_total' we assume that all calls are fine, so leave
        -- the size change list empty
      = do args <- traverse (canonicalise eqs) args
           defs <- get Ctxt
           fn <- getFullName fn_in
           log "totality.termination.sizechange" 10 $ "Looking under "
                  ++ show fn
           aSmaller <- resolved (gamma defs) (NS builtinNS (UN $ Basic "assert_smaller"))
           logC "totality.termination.sizechange" 10 $
               do under <- traverse (\ (n, t) =>
                              pure (n, !(toFullNames !(quoteNF [<] t)))) pats
                  targs <- traverse (\t => toFullNames !(quoteNF [<] t)) args
                  pure ("Under " ++ show under ++ "\n" ++ "Args " ++ show targs)
           if fn == NS builtinNS (UN $ Basic "assert_total")
              then pure []
              else
               do scs <- traverse (findSC g eqs pats) args
                  pure ([MkSCCall fn
                           (expandToArity arity
                                !(traverse (mkChange eqs aSmaller pats) args))]
                           ++ concat scs)

-- Substitute a name with what we know about it.
-- We assume that the name has come from a case pattern, which means we're
-- not going to have to look under binders.
-- We also assume that (despite the 'Glued') it's always a VDCon or VDelay
-- therefore no need to expand apps.
substNameInVal : Name -> Glued vars -> Glued vars -> Core (Glued vars)
-- Only interested in Bound names (that we just made) and so we only need
-- to check the index
substNameInVal (MN _ i') rep tm@(VApp _ Bound (MN _ i) _ _)
    = if i == i' then pure rep else pure tm
substNameInVal n rep (VDCon fc cn t a sp)
    = pure $ VDCon fc cn t a !(substNameInSpine sp)
  where
    substNameInSpine : Spine vars -> Core (Spine vars)
    substNameInSpine [<] = pure [<]
    substNameInSpine (rest :< (fc, c, arg))
        = do rest' <- substNameInSpine rest
             pure (rest' :< (fc, c, substNameInVal n rep !arg))
substNameInVal n rep (VDelay fc r t v)
    = pure $ VDelay fc r !(substNameInVal n rep t) !(substNameInVal n rep v)
substNameInVal n rep tm = pure tm

replaceInArgs : Name -> Glued [<] ->
                List (Nat, Glued [<]) -> Core (List (Nat, Glued [<]))
replaceInArgs v tm [] = pure []
-- -- Don't copy if there's no substitution done!
replaceInArgs v tm ((n, arg) :: args)
    = do arg' <- substNameInVal v tm arg
         if !(scEq arg arg')
            then pure $ (n, arg) :: !(replaceInArgs v tm args)
            else pure $ (n, arg) :: (n, arg') :: !(replaceInArgs v tm args)

expandForced : List (Glued [<], Glued [<]) ->
               List (Nat, Glued [<]) -> Core (List (Nat, Glued [<]))
expandForced [] args = pure args
-- Only useful if the equality evaluated to a bound name that we know about
expandForced ((VApp _ Bound n _ _, tm) :: fs) args
    = expandForced fs !(replaceInArgs n tm args)
expandForced (_ :: fs) args = expandForced fs args


findSCscope : {auto c : Ref Ctxt Defs} ->
              {auto v : Ref SCVar Int} ->
         Guardedness ->
         ForcedEqs ->
         List (Nat, Glued [<]) -> -- LHS args and their position
         Maybe Name -> -- variable we're splitting on (if it is a variable)
         FC -> Glued [<] ->
         (args : _) -> VCaseScope args [<] -> -- case alternative
         Core (List SCCall)
findSCscope g eqs args var fc pat [<] sc
   = do (eqsc, rhs) <- sc
        logC "totality.termination.sizechange" 10 $
            (do tms <- traverse (\ (gx, gy) =>
                            pure (!(toFullNames !(quote [<] gx)),
                                  !(toFullNames !(quote [<] gy)))) eqsc
                pure ("Force equalities " ++ show tms))
        let eqs' = eqsc ++ eqs
        args' <- maybe (pure args) (\v => replaceInArgs v pat args) var
        logNF "totality.termination.sizechange" 10 "RHS" [<] rhs
        findSC g eqs'
               !(traverse (\ (n, arg) => pure (n, !(canonicalise eqs' arg))) args')
               rhs
findSCscope g eqs args var fc pat (cargs :< (c, xn)) sc
   = do varg <- nextVar
        pat' <- the (Core (Glued [<])) $ case pat of
                  VDCon vfc n t a sp =>
                      pure (VDCon vfc n t a (sp :< (fc, c, pure varg)))
                  _ => throw (InternalError "Not a data constructor in findSCscope")
        findSCscope g eqs args var fc pat' cargs (sc (pure varg))

findSCalt : {auto c : Ref Ctxt Defs} ->
            {auto v : Ref SCVar Int} ->
         Guardedness ->
         ForcedEqs ->
         List (Nat, Glued [<]) -> -- LHS args and their position
         Maybe Name -> -- variable we're splitting on (if it is a variable)
         VCaseAlt [<] -> -- case alternative
         Core (List SCCall)
findSCalt g eqs args var (VConCase fc n t cargs sc)
    = findSCscope g eqs args var fc (VDCon fc n t (length cargs) [<]) _ sc
findSCalt g eqs args var (VDelayCase fc ty arg tm)
    = do targ <- nextVar
         varg <- nextVar
         let pat = VDelay fc LUnknown targ varg
         (eqs, rhs) <- tm (pure targ) (pure varg)
         findSC g eqs !(expandForced eqs
                     !(maybe (pure args)
                             (\v => replaceInArgs v pat args) var))
                  rhs
findSCalt g eqs args var (VConstCase fc c tm)
    = findSC g eqs !(maybe (pure args)
                       (\v => replaceInArgs v (VPrimVal fc c) args) var)
               tm
findSCalt g eqs args var (VDefaultCase fc tm) = findSC g eqs args tm

findSCspine : {auto c : Ref Ctxt Defs} ->
         {auto v : Ref SCVar Int} ->
         Guardedness ->
         ForcedEqs ->
         List (Nat, Glued [<]) -> -- LHS args and their position
         Spine [<] ->
         Core (List SCCall)
findSCspine g eqs pats [<] = pure []
findSCspine g eqs pats (sp :< (_, _, v))
    = do vCalls <- findSC g eqs pats !v
         spCalls <- findSCspine g eqs pats sp
         pure (vCalls ++ spCalls)

findSCapp : {auto c : Ref Ctxt Defs} ->
            {auto v : Ref SCVar Int} ->
         Guardedness ->
         ForcedEqs ->
         List (Nat, Glued [<]) -> -- LHS args and their position
         Glued [<] -> -- dealing with cases where this is an application
                      -- of some sort
         Core (List SCCall)
findSCapp g eqs pats (VLocal fc _ _ sp)
    = do args <- traverseSnocList (snd . snd) sp
         scs <- traverseSnocList (findSC g eqs pats) args
         pure (concat scs)
findSCapp g eqs pats (VApp fc Bound _ sp _)
    = do args <- traverseSnocList (snd . snd) sp
         scs <- traverseSnocList (findSC g eqs pats) args
         pure (concat scs)
findSCapp g eqs pats (VApp fc Func fn sp _)
    = do defs <- get Ctxt
         args <- traverseSnocList (snd . snd) sp
         Just ty <- lookupTyExact fn (gamma defs)
            | Nothing => do
                log "totality" 50 $ "Lookup failed"
                findSCcall Unguarded eqs pats fc fn 0 (cast args)
         allg <- allGuarded fn
         -- If it has the all guarded flag, pretend it's a data constructor
         -- Otherwise just carry on as normal
         if allg
            then findSCapp g eqs pats (VDCon fc fn 0 0 sp)
            else case g of
                    -- constructor guarded and delayed, so just check the
                    -- arguments
                    InDelay => findSCspine Unguarded eqs pats sp
                    _ => do arity <- getArity [<] ty
                            findSCcall Unguarded eqs pats fc fn arity (cast args)
  where
    allGuarded : Name -> Core Bool
    allGuarded n
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure False
             pure (AllGuarded `elem` flags gdef)
findSCapp InDelay eqs pats (VDCon fc n t a sp)
    = findSCspine InDelay eqs pats sp
findSCapp Guarded eqs pats (VDCon fc n t a sp)
    = findSCspine Guarded eqs pats sp
findSCapp Toplevel eqs pats (VDCon fc n t a sp)
    = findSCspine Guarded eqs pats sp
findSCapp g eqs pats tm = pure [] -- not an application (TODO: VTCon)

-- If we're Guarded and find a Delay, continue with the argument as InDelay
findSC Guarded eqs pats (VDelay _ LInf _ tm)
    = findSC InDelay eqs pats tm
findSC g eqs args (VLam fc x c p ty sc)
    = do v <- nextVar
         findSC g eqs args !(sc (pure v))
findSC g eqs args (VBind fc n b sc)
    = do v <- nextVar
         pure $ !(findSCbinder b) ++ !(findSC g eqs args !(sc (pure v)))
  where
      findSCbinder : Binder (Glued [<]) -> Core (List SCCall)
      findSCbinder (Let _ c val ty) = findSC Unguarded eqs args val
      findSCbinder _ = pure []
findSC g eqs pats (VDelay _ _ _ tm)
    = findSC g eqs pats tm
findSC g eqs pats (VForce _ _ v sp)
    = do vCalls <- findSC g eqs pats v
         spCalls <- findSCspine Unguarded eqs pats sp
         pure (vCalls ++ spCalls)
findSC g eqs args (VCase fc ct c (VApp _ Bound n [<] _) scTy alts)
    = do altCalls <- traverse (findSCalt g eqs args (Just n)) alts
         pure (concat altCalls)
findSC g eqs args (VCase fc ct c sc scTy alts)
    = do altCalls <- traverse (findSCalt g eqs args Nothing) alts
         scCalls <- findSC Unguarded eqs args (asGlued sc)
         pure (scCalls ++ concat altCalls)
findSC g eqs pats tm = findSCapp g eqs pats tm

findSCTop : {auto c : Ref Ctxt Defs} ->
            {auto v : Ref SCVar Int} ->
            Nat -> List (Nat, Glued [<]) -> Glued [<] -> Core (List SCCall)
findSCTop i args (VLam fc x c p ty sc)
    = do arg <- nextVar
         findSCTop (i + 1) ((i, arg) :: args) !(sc (pure arg))
findSCTop i args def = findSC Toplevel [] (reverse args) def

getSC : {auto c : Ref Ctxt Defs} ->
        Defs -> Def -> Core (List SCCall)
getSC defs (Function _ tm _ _)
   = do ntm <- nfTotality [<] tm
        logNF "totality.termination.sizechange" 5 "From tree" [<] ntm
        v <- newRef SCVar 0
        sc <- findSCTop 0 [] ntm
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

isAssertTotal : Ref Ctxt Defs => Name -> Core Bool
isAssertTotal fn_in =
  do fn <- getFullName fn_in
     pure (fn == NS builtinNS (UN $ Basic "assert_total"))

nameIn : {auto c : Ref Ctxt Defs} ->
         List Name -> NF [<] -> Core Bool
nameIn tyns (VBind fc x b sc)
    = if !(nameIn tyns !(expand (binderType b)))
         then pure True
         else do sc' <- sc (pure (vRef fc Bound (MN ("NAMEIN_" ++ show x) 0)))
                 nameIn tyns !(expand sc')
nameIn tyns (VApp _ nt n args _)
    = do False <- isAssertTotal n
           | True => pure False
         anyM (nameIn tyns) (cast !(traverseSnocList spineVal args))
nameIn tyns (VTCon _ n _ args)
    = if n `elem` tyns
         then pure True
         else do args' <- traverseSnocList spineVal args
                 anyM (nameIn tyns) (cast args')
nameIn tyns (VDCon _ n _ _ args)
    = anyM (nameIn tyns)
           (cast !(traverseSnocList spineVal args))
nameIn tyns (VDelayed fc lr ty) = nameIn tyns !(expand ty)
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
                         pure $ splitParams 0 params !(traverseSnocList spineArg args)
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
         else do sc' <- sc (pure (vRef fc Bound (MN ("POSCHECK_" ++ show x) 1)))
                 posArg tyns !(expand sc')
posArg tyns nf@(VApp _ _ n args _)
    = do False <- isAssertTotal n
           | True => do logNF "totality.positivity" 50 "Trusting an assertion" [<] nf
                        pure IsTerminating
         logNF "totality.positivity" 50 "Found an application" [<] nf
         args <- traverseSnocList spineVal args
         pure $ if !(anyM (nameIn tyns) (cast args))
           then NotTerminating NotStrictlyPositive
           else IsTerminating
posArg tyn (VDelayed _ _ ty) = posArg tyn !(expand ty)
posArg tyn nf
  = do logNF "totality.positivity" 50 "Reached the catchall" [<] nf
       pure IsTerminating

checkPosArgs : {auto c : Ref Ctxt Defs} ->
               List Name -> NF [<] -> Core Terminating
checkPosArgs tyns (VBind fc x (Pi _ _ e ty) sc)
    = case !(posArg tyns !(expand ty)) of
           IsTerminating =>
               do let nm = vRef fc Bound (MN ("POSCHECK_" ++ show x) 0)
                  checkPosArgs tyns !(expand !(sc (pure nm)))
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

blockingAssertTotal : {auto c : Ref Ctxt Defs} -> FC -> Core a -> Core a
blockingAssertTotal loc ma
  = do defs <- get Ctxt
       let at = NS builtinNS (UN $ Basic "assert_total")
       Just _ <- lookupCtxtExact at (gamma defs)
         | Nothing => ma
       setVisibility loc at Private
       a <- ma
       setVisibility loc at Public
       pure a

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
                               t <- blockingAssertTotal loc $ checkData (n :: tns) dcons
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
