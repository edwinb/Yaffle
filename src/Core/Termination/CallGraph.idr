module Core.Termination.CallGraph

import Core.Context
import Core.Context.Log
import Core.Env
import Core.TT
import Core.Evaluate

import Data.SnocList

%default covering

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
           _ => applyAll fc v (cast (map (\ e => (multiplicity e, value e)) sp))
dropLazy val = pure (asGlued val)

-- Equal for the purposes of size change means, ignoring as patterns, all
-- non-metavariable positions are equal
scEq : Value f vars -> Value f' vars -> Core Bool

scEqSpine : Spine vars -> Spine vars -> Core Bool
scEqSpine [<] [<] = pure True
scEqSpine (sp :< x) (sp' :< y)
    = do x' <- value x
         y' <- value y
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
                                (cast !(traverseSnocList value sp))
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
    canonSp (rest :< MkSpineEntry fc c arg)
        = do rest' <- canonSp rest
             pure (rest' :< MkSpineEntry fc c (canonicalise eqs !arg))
-- for matching on types, convert to the form the case tree builder uses
canonicalise eqs (VPrimVal fc (PrT c))
    = pure $ (VTCon fc (UN (Basic $ show c)) 0 [<])
canonicalise eqs (VType fc _)
    = pure $ (VTCon fc (UN (Basic "Type")) 0 [<])
canonicalise eqs val = pure val

-- if the argument is an 'assert_smaller', return the thing it's smaller than
asserted : ForcedEqs -> Name -> Glued [<] -> Core (Maybe (Glued [<]))
asserted eqs aSmaller (VApp _ nt fn [<_, _, e, _] _)
     = if fn == aSmaller
          then Just <$> canonicalise eqs !(value e)
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
                                !(traverse (mkChange eqs aSmaller pats) args))
                           fc]
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
    substNameInSpine (rest :< MkSpineEntry fc c arg)
        = do rest' <- substNameInSpine rest
             pure (rest' :< MkSpineEntry fc c (substNameInVal n rep !arg))
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
                      pure (VDCon vfc n t a (sp :< MkSpineEntry fc c (pure varg)))
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
findSCspine g eqs pats (sp :< e)
    = do vCalls <- findSC g eqs pats !(value e)
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
    = do args <- traverseSnocList value sp
         scs <- traverseSnocList (findSC g eqs pats) args
         pure (concat scs)
findSCapp g eqs pats (VApp fc Bound _ sp _)
    = do args <- traverseSnocList value sp
         scs <- traverseSnocList (findSC g eqs pats) args
         pure (concat scs)
findSCapp g eqs pats (VApp fc Func fn sp _)
    = do defs <- get Ctxt
         args <- traverseSnocList value sp
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
         findSC g eqs args !(sc v)
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
         findSCTop (i + 1) ((i, arg) :: args) !(sc arg)
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
