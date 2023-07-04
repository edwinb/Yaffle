module Core.Evaluate.Normalise

import Core.Core
import Core.Context
import Core.Context.Log
import Core.Env
import Core.Error
import Core.Evaluate.Value
import Core.Primitives
import Core.TT

import Data.List
import Data.SnocList
import Data.Vect

data EvalFlags
    = Full
    | KeepAs -- keep @ patterns, don't expand any 'let' in the environment
    | KeepLet -- don't expand any 'let' at all, just expand 'alwaysInline'
    | Totality

export
apply : FC -> Value f vars -> RigCount -> Core (Glued vars) -> Core (Glued vars)
apply fc (VLam _ _ _ _ _ sc) _ arg = sc !arg
-- might happen if we're in KeepLet mode
apply fc (VBind bfc x (Let lfc c val ty) sc) q arg
    = pure $ VBind bfc x (Let lfc c val ty)
                   (\val' => apply fc !(sc val') q arg)
apply fc (VApp afc nt n spine go) q arg
    = pure $ VApp afc nt n (spine :< MkSpineEntry fc q arg) $
           do Just go' <- go
                   | Nothing => pure Nothing
              res <- apply fc go' q arg
              pure (Just res)
apply fc (VLocal lfc idx p spine) q arg
    = pure $ VLocal lfc idx p (spine :< MkSpineEntry fc q arg)
apply fc (VMeta mfc n i sc spine go) q arg
    = pure $ VMeta mfc n i sc (spine :< MkSpineEntry fc q arg) $
           do Just go' <- go
                   | Nothing => pure Nothing
              res <- apply fc go' q arg
              pure (Just res)
apply fc (VDCon dfc n t a spine) q arg
    = pure $ VDCon dfc n t a (spine :< MkSpineEntry fc q arg)
apply fc (VTCon tfc n a spine) q arg
    = pure $ VTCon tfc n a (spine :< MkSpineEntry fc q arg)
apply fc (VAs _ _ _ pat) q arg
    = apply fc pat q arg -- doesn't really make sense to keep the name
apply fc (VForce ffc r v spine) q arg
    = pure $ VForce ffc r v (spine :< MkSpineEntry fc q arg)
apply fc (VCase cfc t r sc ty alts) q arg
    = pure $ VCase cfc t r sc ty !(traverse (applyAlt arg) alts)
  where
    applyConCase : Core (Glued vars) ->
                   Name -> Int ->
                   (args : SnocList (RigCount, Name)) ->
                   VCaseScope args vars ->
                   VCaseScope args vars
    applyConCase arg n t [<] rhs
        = do (fs, rhs') <- rhs
             sc <- apply fc rhs' q arg
             pure (fs, sc)
    applyConCase arg n t (args :< (r, a)) sc
        = \a' => applyConCase arg n t args (sc a')

    -- Need to apply the argument to the rhs of every case branch
    applyAlt : Core (Glued vars) -> VCaseAlt vars -> Core (VCaseAlt vars)
    applyAlt arg (VConCase fc n t args rhs)
        = pure $ VConCase fc n t args (applyConCase arg n t args rhs)
    applyAlt arg (VDelayCase fc t a rhs)
        = pure $ VDelayCase fc t a
                  (\t', a' =>
                      do (fs, rhs') <- rhs t' a'
                         sc <- apply fc rhs' q arg
                         pure (fs, sc))
    applyAlt arg (VConstCase fc c rhs) = VConstCase fc c <$> apply fc rhs q arg
    applyAlt arg (VDefaultCase fc rhs) = VDefaultCase fc <$> apply fc rhs q arg
-- Remaining cases would be ill-typed
apply _ arg _ _ = pure (believe_me arg)

export
applyAll : FC -> Glued vars -> List (RigCount, Core (Glued vars)) -> Core (Glued vars)
applyAll fc f [] = pure f
applyAll fc f ((q, x) :: xs)
    = do f' <- apply fc f q x
         applyAll fc f' xs

data LocalEnv : SnocList Name -> SnocList Name -> Type where
     Lin : LocalEnv [<] vars
     (:<) : LocalEnv free vars -> Core (Glued vars) -> LocalEnv (free :< x) vars

extend : LocalEnv ns vars -> LocalEnv ms vars -> LocalEnv (ms ++ ns) vars
extend [<] env = env
extend (vars :< x) env = extend vars env :< x

updateEnv : {idx : _} ->
            LocalEnv free vars ->
            (0 _ : IsVar n idx (vars ++ free)) -> Core (Glued vars) ->
            LocalEnv free vars
updateEnv (env :< b) First new = env :< new
updateEnv (env :< b) (Later p) new = updateEnv env p new :< b
updateEnv env _ _ = env

namespace ExtendLocs
  public export
  data ExtendLocs : SnocList Name -> SnocList Name -> Type where
       Lin : ExtendLocs vars [<]
       (:<) : ExtendLocs vars xs -> Core (Glued vars) -> ExtendLocs vars (cons x xs)

mkEnv : ExtendLocs vars ns -> LocalEnv ns vars
mkEnv {vars} ext = rewrite sym (appendLinLeftNeutral ns) in go ext [<]
  where
    go : ExtendLocs vars ns' -> LocalEnv rest vars ->
         LocalEnv (rest ++ ns') vars
    go [<] locs = locs
    go {ns' = cons x xs} {rest} (ext :< val) locs
        = rewrite appendAssociative rest [<x] xs in
                  go ext (locs :< val)

parameters {auto c : Ref Ctxt Defs} (eflags : EvalFlags)

  runOp : {ar : _} ->
          FC -> PrimFn ar -> Vect ar (Glued vars) -> Core (NF vars)
  runOp fc op args
      = do args' <- traverseVect expand args
           -- If it gets stuck, return the glued args, not the values
           case getOp op args' of
             Just res => pure res
             Nothing => do pure $ VPrimOp fc op args

  -- Forward declared since these are all mutual
  export
  eval : LocalEnv free vars ->
         Env Term vars ->
         Term (vars ++ free) -> Core (Glued vars)

  evalCaseAlt : LocalEnv free vars -> Env Term vars ->
                CaseAlt (vars ++ free) ->
                Core (VCaseAlt vars)
  evalCaseAlt {vars} {free} locs env (ConCase fc n tag scope)
      = pure $ VConCase fc n tag _ (getScope locs scope)
    where
      CaseArgs : CaseScope vs -> SnocList (RigCount, Name)
      CaseArgs (RHS _ tm) = [<]
      CaseArgs (Arg r x sc) = CaseArgs sc :< (r, x)

      evalForced : forall free .
                   LocalEnv free vars ->
                   (Var (vars ++ free), Term (vars ++ free)) ->
                   Core (Glued vars, Glued vars)
      evalForced locs (MkVar v, tm)
          = do v' <- eval locs env (Local fc _ v)
               tm' <- eval locs env tm
               pure (v', tm')

      getScope : forall free .
                 LocalEnv free vars ->
                 (sc : CaseScope (vars ++ free)) ->
                 VCaseScope (CaseArgs sc) vars
      getScope locs (RHS fs tm)
          = do tm' <- eval locs env tm
               fs' <- traverse (evalForced locs) fs
               pure (fs', tm')
      getScope locs (Arg r x sc) = \v => getScope (locs :< v) sc

  evalCaseAlt locs env (DelayCase fc t a tm)
      = pure $ VDelayCase fc t a
                 (\t', a' => pure ([], !(eval (locs :< a' :< t') env tm)))
  evalCaseAlt locs env (ConstCase fc c tm)
      = pure $ VConstCase fc c !(eval locs env tm)
  evalCaseAlt locs env (DefaultCase fc tm)
      = pure $ VDefaultCase fc !(eval locs env tm)

  blockedCase : FC -> LocalEnv free vars -> Env Term vars ->
                CaseType -> RigCount ->
                (sc : NF vars) -> (scTy : Term (vars ++ free)) ->
                List (CaseAlt (vars ++ free)) ->
                Core (Glued vars)
  blockedCase fc locs env t r sc scTy alts
      = do scTy' <- eval locs env scTy
           alts' <- traverse (evalCaseAlt locs env) alts
           pure (VCase fc t r sc scTy' alts')

  -- We've turned the spine into a list so that the argument positions
  -- correspond when going through the CaseScope
  evalCaseScope : LocalEnv free vars -> Env Term vars ->
                  List (SpineEntry vars) -> CaseScope (vars ++ free) ->
                  Core (Glued vars) -> -- what to do if stuck
                  Core (Glued vars)
  evalCaseScope locs env [] (RHS _ tm) stuck = eval locs env tm
  evalCaseScope locs env (e :: sp) (Arg r x sc) stuck
      = evalCaseScope (locs :< value e) env sp sc stuck
  evalCaseScope _ _ _ _ stuck = stuck

  tryAlt : LocalEnv free vars -> Env Term vars ->
           (sc : NF vars) -> -- scrutinee, which we assume to be in
                 -- canonical form since we've checked (so not blocked)
           (CaseAlt (vars ++ free)) ->
           Core (Glued vars) -> -- what to do if stuck
           Maybe (Core (Glued vars))
  tryAlt locs env sc (DefaultCase _ rhs) stuck = Just (eval locs env rhs)
  tryAlt {vars} locs env (VDCon _ _ t a sp) (ConCase _ _ t' cscope) stuck
      = if t == t' then Just (evalCaseScope locs env (cast sp) cscope stuck)
           else Nothing
  tryAlt {vars} locs env (VTCon _ n a sp) (ConCase _ n' _ cscope) stuck
      = if n == n' then Just (evalCaseScope locs env (cast sp) cscope stuck)
           else Nothing
  tryAlt locs env (VDelay _ _ ty arg) (DelayCase _ ty' arg' rhs) stuck
      = Just (eval (locs :< pure ty :< pure arg) env rhs)
  tryAlt locs env (VPrimVal _ c) (ConstCase _ c' rhs) stuck
      = if c == c'
           then Just (eval locs env rhs)
           else Nothing
  tryAlt locs env (VErased _ (Dotted v)) alt stuck
      = tryAlt locs env v alt stuck
  tryAlt _ _ _ _ _ = Nothing

  tryAlts : LocalEnv free vars -> Env Term vars ->
            (sc : NF vars) -> -- scrutinee, which we assume to be in
                  -- canonical form since we've checked (so not blocked)
            List (CaseAlt (vars ++ free)) ->
            Core (Glued vars) -> -- what to do if stuck
            Core (Glued vars)
  tryAlts locs env sc (a :: alts) stuck
      = case tryAlt locs env sc a stuck of
             Nothing => tryAlts locs env sc alts stuck
             Just res => res
  tryAlts locs env sc [] stuck = stuck

  evalCaseBlock
           : FC -> LocalEnv free vars -> Env Term vars ->
             CaseType -> RigCount -> (sc : NF vars) -> (scTy : Term (vars ++ free)) ->
             List (CaseAlt (vars ++ free)) ->
             Core (Glued vars)
  evalCaseBlock fc locs env t r sc ty alts
      = if isCanonical sc
           then tryAlts locs env sc alts (blockedCase fc locs env t r sc ty alts)
           else blockedCase fc locs env t r sc ty alts
    where
      isCanonical : NF vars -> Bool
      isCanonical (VLam{}) = True
      isCanonical (VBind{}) = True
      isCanonical (VDCon{}) = True
      isCanonical (VTCon{}) = True
      isCanonical (VDelay{}) = True
      isCanonical (VPrimVal{}) = True
      isCanonical (VType{}) = True
      isCanonical (VErased _ (Dotted t)) = isCanonical t
      isCanonical _ = False

  evalCase : LocalEnv free vars ->
             Env Term vars ->
             FC -> CaseType -> RigCount ->
             Term (vars ++ free) -> Term (vars ++ free) ->
             List (CaseAlt (vars ++ free)) -> Core (Glued vars)
  evalCase locs env fc t r sc ty alts
      = do sc' <- case eflags of
                       -- Don't expand in totality mode or we might reduce too
                       -- much
                       Totality => believe_me $ eval locs env sc
                       _ => expand !(eval locs env sc)
           locs' <- case sc of
                         Local _ _ p => pure $ updateEnv locs p (pure (asGlued sc'))
                         _ => pure locs
           evalCaseBlock fc locs' env t r (stripAs sc') ty alts
    where
      stripAs : Value f vars -> Value f vars
      stripAs (VAs _ _ _ p) = stripAs p
      stripAs x = x

  evalLocal : {idx : _} ->
              Env Term vars ->
              FC -> (0 p : IsVar n idx (vars ++ free)) ->
              LocalEnv free vars ->
              Core (Glued vars)
  evalLocal env fc p [<]
      = let loc = VLocal fc _ p [<] in
        if keepBinder eflags
           then pure loc
           else case getLet p env of
                     Nothing => pure loc
                     Just val => eval [<] env val
    where
      keepBinder : EvalFlags -> Bool
      keepBinder KeepAs = True
      keepBinder KeepLet = True
      keepBinder _ = False
  evalLocal env fc First (locs :< x) = x
  evalLocal env fc (Later p) (locs :< x) = evalLocal env fc p locs

  evalPiInfo : LocalEnv free vars ->
               Env Term vars ->
               PiInfo (Term (vars ++ free)) ->
               Core (PiInfo (Glued vars))
  evalPiInfo locs env Implicit = pure Implicit
  evalPiInfo locs env Explicit = pure Explicit
  evalPiInfo locs env AutoImplicit = pure AutoImplicit
  evalPiInfo locs env (DefImplicit x)
      = do x' <- eval locs env x
           pure (DefImplicit x')

  evalBinder : LocalEnv free vars ->
               Env Term vars ->
               Binder (Term (vars ++ free)) ->
               Core (Binder (Glued vars))
  evalBinder locs env (Lam fc c p ty)
     = pure $ Lam fc c !(evalPiInfo locs env p) !(eval locs env ty)
  evalBinder locs env (Let fc c val ty)
     = pure $ Let fc c !(eval locs env val) !(eval locs env ty)
  evalBinder locs env (Pi fc c p ty)
     = pure $ Pi fc c !(evalPiInfo locs env p) !(eval locs env ty)
  evalBinder locs env (PVar fc c p ty)
     = pure $ PVar fc c !(evalPiInfo locs env p) !(eval locs env ty)
  evalBinder locs env (PLet fc c val ty)
     = pure $ PLet fc c !(eval locs env val) !(eval locs env ty)
  evalBinder locs env (PVTy fc c ty)
     = pure $ PVTy fc c !(eval locs env ty)

  evalMeta : LocalEnv free vars ->
             Env Term vars ->
             FC -> Name -> Int -> List (RigCount, Term (vars ++ free)) ->
             Core (Glued vars)
  evalMeta locs env fc n i scope
       = do scope' <- traverse (\ (q, val) =>
                                     do let val' = eval locs env val
                                        pure (q, val')) scope
            defs <- get Ctxt
            Just def <- lookupCtxtExact n (gamma defs)
                 | Nothing => pure (VMeta fc n i scope' [<] (pure Nothing))
            let Function fi fn _ _ = definition def
                 | _ => pure (VMeta fc n i scope' [<] (pure Nothing))
            if alwaysReduce fi || (reduceForTC eflags (multiplicity def))
               then do evalfn <- eval locs env (embed fn)
                       applyAll fc evalfn scope'
               else pure $ VMeta fc n i scope' [<] $
                       do evalfn <- eval locs env (embed fn)
                          res <- applyAll fc evalfn scope'
                          pure (Just res)
    where
      reduceForTC : EvalFlags -> RigCount -> Bool
      reduceForTC Totality c = not (isErased c)
      reduceForTC _ _ = False

  evalRef : LocalEnv free vars ->
            Env Term vars ->
            FC -> NameType -> Name ->
            Core (Glued vars)
  evalRef locs env fc (DataCon t a) n
      = pure $ VDCon fc n t a [<]
  evalRef locs env fc (TyCon a) n
      = pure $ VTCon fc n a [<]
  evalRef locs env fc nt n
      = do defs <- get Ctxt
           Just def <- lookupCtxtExact n (gamma defs)
                | Nothing => pure (VApp fc nt n [<] (pure Nothing))
           let Function fi fn _ _ = definition def
                | _ => pure (VApp fc nt n [<] (pure Nothing))
           if alwaysReduce fi || (reduceForTC eflags (flags def))
              then eval locs env (embed fn)
              else pure $ VApp fc nt n [<] $
                          do res <- eval locs env (embed fn)
                             pure (Just res)
    where
      reduceForTC : EvalFlags -> List DefFlag -> Bool
      reduceForTC Totality f = elem TCInline f
      reduceForTC _ _ = False

  evalBind : LocalEnv free vars ->
         Env Term vars ->
         FC -> (x : Name) -> (b : Binder (Term (vars ++ free))) ->
         (scope : (Term ((vars ++ free) :< x))) ->
         Core (Glued vars)
  evalBind locs env fc x (Lam bfc r p ty) sc
      = pure $ VLam fc x r !(evalPiInfo locs env p) !(eval locs env ty)
                        (\arg => eval (locs :< pure arg) env sc)
  evalBind locs env fc x b@(Let bfc c val ty) sc
      = case eflags of
             KeepLet =>
                  pure $ VBind fc x !(evalBinder locs env b)
                               (\arg => eval (locs :< arg) env sc)
             _ => do val' <- eval locs env val
                     eval (locs :< pure val') env sc
  evalBind locs env fc x b sc
      = pure $ VBind fc x !(evalBinder locs env b)
                     (\arg => eval (locs :< arg) env sc)

  evalForce : LocalEnv free vars ->
              Env Term vars ->
              FC -> LazyReason -> Term (vars ++ free) ->
              Core (Glued vars)
  evalForce locs env fc r tm =
      do val <- eval locs env tm
         VDelay _ _ _ arg <- expand val
             | tm' => pure $ VForce fc r val [<]
         pure arg

  evalPrimOp : {arity : _} ->
               LocalEnv free vars ->
               Env Term vars ->
               FC -> PrimFn arity -> Vect arity (Term (vars ++ free)) ->
               Core (Glued vars)
  evalPrimOp {free} {vars} locs env fc op args
      = do nf <- runOp fc op !(evalArgs args)
           pure (believe_me nf) -- switch back to Glued
    where
      -- No traverse for Vect in Core...
      evalArgs : Vect n (Term (vars ++ free)) -> Core (Vect n (Glued vars))
      evalArgs [] = pure []
      evalArgs (a :: as) = pure $ !(eval locs env a) :: !(evalArgs as)

--   Declared above with this type:
--   eval : LocalEnv free vars ->
--          Env Term vars ->
--          Term (vars ++ free) -> Core (Glued vars)
  eval locs env (Local fc idx p) = evalLocal env fc p locs
  eval locs env (Ref fc nt n) = evalRef locs env fc nt n
  eval locs env (Meta fc n i scope)
       = evalMeta locs env fc n i scope
  eval locs env (Bind fc x b sc) = evalBind locs env fc x b sc
  eval locs env tm@(App fc fn q arg)
      = apply fc !(eval locs env fn) q (eval locs env arg)
  eval locs env (As fc use as pat)
      = case eflags of
             KeepAs => pure $ VAs fc use !(eval locs env as)
                                         !(eval locs env pat)
             KeepLet => pure $ VAs fc use !(eval locs env as)
                                          !(eval locs env pat)
             _ => eval locs env pat
  eval locs env (Case fc t r sc ty alts)
      = evalCase locs env fc t r sc ty alts
  eval locs env (TDelayed fc r tm)
      = pure $ VDelayed fc r !(eval locs env tm)
  eval locs env (TDelay fc r ty arg)
      = pure $ VDelay fc r !(eval locs env ty) !(eval locs env arg)
  eval locs env (TForce fc r tm)
      = evalForce locs env fc r tm
  eval locs env (PrimVal fc c) = pure $ VPrimVal fc c
  eval {free} {vars} locs env (PrimOp fc op args)
      = evalPrimOp locs env fc op args
  eval locs env (Erased fc why) = VErased fc <$> traverse @{%search} @{CORE} (eval locs env) why
  eval locs env (Unmatched fc str) = pure $ VUnmatched fc str
  eval locs env (TType fc n) = pure $ VType fc n

parameters {auto c : Ref Ctxt Defs}

  export
  nf : Env Term vars -> Term vars -> Core (Glued vars)
  nf = eval Full [<]

  export
  nfLHS : Env Term vars -> Term vars -> Core (Glued vars)
  nfLHS = eval KeepAs [<]

  export
  nfKeepLet : Env Term vars -> Term vars -> Core (Glued vars)
  nfKeepLet = eval KeepLet [<]

  export
  nfTotality : Env Term vars -> Term vars -> Core (Glued vars)
  nfTotality = eval Totality [<]
