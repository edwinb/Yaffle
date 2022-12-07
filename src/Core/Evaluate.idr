module Core.Evaluate

import Core.Context
import Core.Context.Log
import Core.Env
import Core.Error
import public Core.Evaluate.Convert
import public Core.Evaluate.Normalise
import public Core.Evaluate.Quote
import public Core.Evaluate.Value
import Core.TT

import Data.SnocList

parameters {auto c : Ref Ctxt Defs}
  export
  normalise
      : {vars : _} ->
        Env Term vars -> Term vars -> Core (Term vars)
  normalise env tm
      = do val <- nf env tm
           quoteNF env val

  export
  normaliseHNF
      : {vars : _} ->
        Env Term vars -> Term vars -> Core (Term vars)
  normaliseHNF env tm
      = do val <- nf env tm
           quoteHNF env val

  export
  normaliseAll
      : {vars : _} ->
        Env Term vars -> Term vars -> Core (Term vars)
  normaliseAll env tm
      = do val <- nf env tm
           quoteNFall env val

  export
  normaliseHNFall
      : {vars : _} ->
        Env Term vars -> Term vars -> Core (Term vars)
  normaliseHNFall env tm
      = do val <- nf env tm
           quoteHNFall env val

  export
  normaliseHoles
      : {vars : _} ->
        Env Term vars -> Term vars -> Core (Term vars)
  normaliseHoles env tm
      = do val <- nf env tm
           quoteHoles env val

  export
  normaliseLHS
      : {vars : _} ->
        Env Term vars -> Term vars -> Core (Term vars)
  normaliseLHS env tm
      = do val <- nfLHS env tm
           quoteHoles env val

  export
  normaliseBinders
      : {vars : _} ->
        Env Term vars -> Term vars -> Core (Term vars)
  normaliseBinders env tm
      = do val <- nf env tm
           quoteBinders env val

  -- Normalise, but without normalising the types of binders.
  export
  normaliseScope : {vars : _} ->
                   Env Term vars -> Term vars -> Core (Term vars)
  normaliseScope env (Bind fc n b sc)
      = pure $ Bind fc n b !(normaliseScope (env :< b) sc)
  normaliseScope env tm = normalise env tm

  export
  normaliseHolesScope : {vars : _} ->
                   Env Term vars -> Term vars -> Core (Term vars)
  normaliseHolesScope env (Bind fc n b sc)
      = pure $ Bind fc n b !(normaliseHolesScope (env :< b) sc)
  normaliseHolesScope env tm = normaliseHoles env tm

  export
  getArityVal : NF vars -> Core Nat
  getArityVal (VBind fc _ (Pi _ _ _ _) sc)
      = pure $ 1 + !(getArityVal !(expand !(sc (VErased fc Placeholder))))
  getArityVal _ = pure 0

  export
  getArity : {vars : _} -> Env Term vars -> Term vars -> Core Nat
  getArity env tm = getArityVal !(expand !(nf env tm))

  replace'
      : {vars : _} ->
        (expandGlued : Bool) -> Int -> Env Term vars ->
        (orig : Value f vars) -> (parg : Term vars) -> (tm : Value f' vars) ->
        Core (Term vars)
  replace' {vars} expand tmpi env orig parg tm
      = if !(convert env orig tm)
           then pure parg
           else repSub tm
    where
      repArg : Value f vars -> Core (Term vars)
      repArg = replace' expand tmpi env orig parg

      repArgAll : Spine vars -> Core (SnocList (FC, RigCount, Term vars))
      repArgAll [<] = pure [<]
      repArgAll (xs :< (f, r, tm))
          = do xs' <- repArgAll xs
               tm' <- repArg tm
               pure (xs' :< (f, r, tm'))

      repScope : FC -> Int -> (args : SnocList (RigCount, Name)) ->
                 VCaseScope args vars -> Core (CaseScope vars)
      repScope fc tmpi [<] rhs
          = do -- Stop expanding or recursive functions will go forever
               rhs' <- replace' False tmpi env orig parg !rhs
               pure (RHS rhs')
      repScope fc tmpi (xs :< (r, x)) scope
          = do let xn = MN "tmp" tmpi
               let xv = VApp fc Bound xn [<] (pure Nothing)
               scope' <- repScope fc (tmpi + 1) xs (scope xv)
               pure (Arg r x (refsToLocalsCaseScope (Add x xn None) scope'))

      repAlt : VCaseAlt vars -> Core (CaseAlt vars)
      repAlt (VConCase fc n t args scope)
          = do scope' <- repScope fc tmpi args scope
               pure (ConCase fc n t scope')
      repAlt (VDelayCase fc ty arg scope)
          = do let tyn = MN "tmp" tmpi
               let argn = MN "tmp" (tmpi + 1)
               let tyv = VApp fc Bound tyn [<] (pure Nothing)
               let argv = VApp fc Bound argn [<] (pure Nothing)
               -- Stop expanding or recursive functions will go forever
               scope' <- replace' False (tmpi + 2) env orig parg !(scope tyv argv)
               let rhs = refsToLocals (Add ty tyn (Add arg argn None)) scope'
               pure (DelayCase fc ty arg rhs)
      repAlt (VConstCase fc c rhs)
          = do rhs' <- repArg rhs
               pure (ConstCase fc c rhs')
      repAlt (VDefaultCase fc rhs)
          = do rhs' <- repArg rhs
               pure (DefaultCase fc rhs')

      repSub : Value f vars -> Core (Term vars)
      repSub (VLam fc x c p ty scfn)
          = do b' <- traverse repSub (Lam fc c p ty)
               let x' = MN "tmp" tmpi
               let var = VApp fc Bound x' [<] (pure Nothing)
               sc' <- replace' expand (tmpi + 1) env orig parg !(scfn var)
               pure (Bind fc x b' (refsToLocals (Add x x' None) sc'))
      repSub (VBind fc x b scfn)
          = do b' <- traverse repSub b
               let x' = MN "tmp" tmpi
               let var = VApp fc Bound x' [<] (pure Nothing)
               sc' <- replace' expand (tmpi + 1) env orig parg !(scfn var)
               pure (Bind fc x b' (refsToLocals (Add x x' None) sc'))
      repSub (VApp fc nt fn args val')
          = if expand
               then do Just nf <- val'
                            | Nothing =>
                             do args' <- repArgAll args
                                pure $ applyWithFC (Ref fc nt fn) (toList args')
                       {- unprincipled but works:
                       case nf of
                         VCase{} => do args' <- repArgAll args
                                       pure $ applyWithFC (Ref fc nt fn) (toList args')
                         _ => repSub nf -}

                       {- principled but does not work: with001 gives us a puzzling error
                          message arguing that
                                  g (f t)
                          and     case f t of { Z => Z; S n => S (g n) }
                          are not convertible
                       -}
                       replace' expand tmpi env orig parg nf
               else do args' <- repArgAll args
                       pure $ applyWithFC (Ref fc nt fn) (toList args')
      repSub (VLocal fc idx p args)
          = do args' <- repArgAll args
               pure $ applyWithFC (Local fc idx p) (toList args')
      -- Look in value of the metavar if it's solved, otherwise leave it
      repSub (VMeta fc n i scope args val)
          = do Nothing <- val
                   | Just val' => repSub val'
               sc' <- traverse (\ (q, tm) => do tm' <- repArg tm
                                                pure (q, tm')) scope
               args' <- repArgAll args
               pure $ applyWithFC (Meta fc n i sc') (toList args')
      repSub (VDCon fc n t a args)
        = do args' <- repArgAll args
             pure $ applyWithFC (Ref fc (DataCon t a) n) (toList args')
      repSub (VTCon fc n a args)
        = do args' <- repArgAll args
             pure $ applyWithFC (Ref fc (TyCon a) n) (toList args')
      repSub (VAs fc s a pat)
          = do a' <- repSub a
               pat' <- repSub pat
               pure (As fc s a' pat')
      repSub (VCase fc r sc scty alts)
          = do sc' <- repArg sc
               scty' <- repArg scty
               alts' <- traverse repAlt alts
               pure (Case fc r sc' scty' alts')
      repSub (VDelayed fc r tm)
          = do tm' <- repSub tm
               pure (TDelayed fc r tm')
      repSub (VDelay fc r ty tm)
          = do ty' <- repArg ty
               tm' <- repArg tm
               pure (TDelay fc r ty' tm')
      repSub (VForce fc r tm args)
          = do args' <- repArgAll args
               tm' <- repSub tm
               pure $ applyWithFC (TForce fc r tm') (toList args')
      repSub tm = quote env tm

  export
  replace
      : {vars : _} ->
        Env Term vars ->
        (orig : Value f vars) -> (new : Term vars) -> (tm : Value f' vars) ->
        Core (Term vars)
  replace = replace' True 0

  export
  replaceSyn
      : {vars : _} ->
        Env Term vars ->
        (orig : Value f vars) -> (new : Term vars) -> (tm : Value f' vars) ->
        Core (Term vars)
  replaceSyn = replace' False 0

  -- If the term is an application of a primitive conversion (fromInteger etc)
  -- and it's applied to a constant, fully normalise the term.
  export
  normalisePrims : {vs : _} ->
                   -- size heuristic for when to unfold
                   (Constant -> Bool) ->
                   -- view to check whether an argument is a constant
                   (arg -> Maybe Constant) ->
                   -- Reduce everything (True) or just public export (False)
                   Bool ->
                   -- list of primitives
                   List Name ->
                   -- view of the potential redex
                   (n : Name) ->          -- function name
                   (args : SnocList arg) ->   -- arguments from inside out (arg1, ..., argk)
                   -- actual term to evaluate if needed
                   (tm : Term vs) ->      -- original term (n arg1 ... argk)
                   Env Term vs ->         -- evaluation environment
                   -- output only evaluated if primitive
                   Core (Maybe (Term vs))
  normalisePrims boundSafe viewConstant all prims n args tm env
     = do let True = isPrimName prims !(getFullName n) -- is a primitive
                | _ => pure Nothing
          let (_ :< mc) = reverse args -- with at least one argument
                | _ => pure Nothing
          let (Just c) = viewConstant mc -- that is a constant
                | _ => pure Nothing
          let True = boundSafe c -- that we should expand
                | _ => pure Nothing
          tm <- if all
                   then normaliseAll env tm
                   else normalise env tm
          pure (Just tm)

  export
  etaContract : {vars : _} -> Term vars -> Core (Term vars)
  etaContract tm = do
    defs <- get Ctxt
    logTerm "eval.eta" 5 "Attempting to eta contract subterms of" tm
    nf <- normalise (mkEnv EmptyFC _) tm
    logTerm "eval.eta" 5 "Evaluated to" nf
    res <- mapTermM act tm
    logTerm "eval.eta" 5 "Result of eta-contraction" res
    pure res

     where

      act : {vars : _} -> Term vars -> Core (Term vars)
      act tm = do
        logTerm "eval.eta" 10 "  Considering" tm
        case tm of
          (Bind _ x (Lam _ _ _ _) (App _ fn _ (Local _ Z _))) => do
            logTerm "eval.eta" 10 "  Shrinking candidate" fn
            let shrunk = shrinkTerm fn (DropCons SubRefl)
            case shrunk of
              Nothing => do
                log "eval.eta" 10 "  Failure!"
                pure tm
              Just tm' => do
                logTerm "eval.eta" 10 "  Success!" tm'
                pure tm'
          _ => pure tm

  -- Log message with a value, translating back to human readable names first
  export
  logNF : {vars : _} ->
          (s : String) ->
          {auto 0 _ : KnownTopic s} ->
          Nat -> Lazy String -> Env Term vars -> Value f vars -> Core ()
  logNF str n msg env tmnf
      = when !(logging str n) $
          do tm <- quote env tmnf
             tm' <- toFullNames tm
             logString str n (msg ++ ": " ++ show tm')

  -- Log message with a term, reducing holes and translating back to human
  -- readable names first
  export
  logTermNF' : {vars : _} ->
               (s : String) ->
               {auto 0 _ : KnownTopic s} ->
               Nat -> Lazy String -> Env Term vars -> Term vars -> Core ()
  logTermNF' str n msg env tm
      = do defs <- get Ctxt
           tmnf <- normalise env tm
           tm' <- toFullNames tmnf
           logString str n (msg ++ ": " ++ show tm')

  export
  logTermNF : {vars : _} ->
              (s : String) ->
              {auto 0 _ : KnownTopic s} ->
              Nat -> Lazy String -> Env Term vars -> Term vars -> Core ()
  logTermNF str n msg env tm
      = when !(logging str n) $ logTermNF' str n msg env tm

  export
  logEnv : {vars : _} ->
           (s : String) ->
           {auto 0 _ : KnownTopic s} ->
           Nat -> String -> Env Term vars -> Core ()
  logEnv str n msg env
      = when !(logging str n) $
          do logString str n msg
             dumpEnv env
    where
      dumpEnv : {vs : SnocList Name} -> Env Term vs -> Core ()
      dumpEnv [<] = pure ()
      dumpEnv {vs = _ :< x} (bs :< Let _ c val ty)
          = do logTermNF' str n (msg ++ ": let " ++ show x) bs val
               logTermNF' str n (msg ++ ":" ++ show c ++ " " ++ show x) bs ty
               dumpEnv bs
      dumpEnv {vs = _ :< x} (bs :< b)
          = do logTermNF' str n (msg ++ ":" ++ show (multiplicity b) ++ " " ++
                             show (piInfo b) ++ " " ++
                             show x) bs (binderType b)
               dumpEnv bs
