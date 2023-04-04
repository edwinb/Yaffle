module Compiler.CaseOpts

-- Case block related transformations

import Compiler.CompileExpr

import Core.CompileExpr
import Core.Context
import Core.FC
import Core.TT

import Data.List
import Data.Vect

%default covering

{-
Lifting out lambdas:

case t of
     C1 => \x1 => e1
     ...
     Cn => \xn = en

  where every branch begins with a lambda, can become:

\x => case t of
           C1 => e1[x/x1]
           ,,,
           Cn => en[x/xn]
-}

shiftUnder : {args : _} ->
             {idx : _} ->
             (0 p : IsVar n idx (vars ++ args :< x)) ->
             NVar n (vars :< x ++ args)
shiftUnder First = weakenNVar (mkSizeOf args) (MkNVar First)
shiftUnder (Later p) = insertNVar (mkSizeOf args) (MkNVar p)

shiftVar : {outer, args : _} ->
           {idx : _} ->
           (0 p : IsVar n idx ((vars ++ args :< x) ++ outer)) ->
           NVar n ((vars :< x ++ args) ++ outer)
shiftVar {outer = [<]} p = shiftUnder p
shiftVar {outer = (xs :< n)} First = MkNVar First
shiftVar {outer = (xs :< y)} (Later p)
    = case shiftVar p of
           MkNVar p' => MkNVar (Later p')

mutual
  shiftBinder : {outer, args : _} ->
                (new : Name) ->
                CExp ((vars ++ args) :< old ++ outer) ->
                CExp ((vars :< new ++ args) ++ outer)
  shiftBinder new (CLocal fc p)
      = case shiftVar p of
             MkNVar p' => CLocal fc (renameVar p')
    where
      renameVar : IsVar x i (((rest :< old) ++ args) ++ outer) ->
                  IsVar x i (((rest :< new) ++ args) ++ outer)
      renameVar = believe_me -- it's the same index, so just the identity at run time
  shiftBinder new (CRef fc n) = CRef fc n
  shiftBinder {outer} new (CLam fc n sc)
      = CLam fc n $ shiftBinder {outer = outer :< n} new sc
  shiftBinder new (CLet fc n inlineOK val sc)
      = CLet fc n inlineOK (shiftBinder new val)
                           $ shiftBinder {outer = outer :< n} new sc
  shiftBinder new (CApp fc f args)
      = CApp fc (shiftBinder new f) $ map (shiftBinder new) args
  shiftBinder new (CCon fc ci c tag args)
      = CCon fc ci c tag $ map (shiftBinder new) args
  shiftBinder new (COp fc op args) = COp fc op $ map (shiftBinder new) args
  shiftBinder new (CExtPrim fc p args)
      = CExtPrim fc p $ map (shiftBinder new) args
  shiftBinder new (CForce fc r arg) = CForce fc r $ shiftBinder new arg
  shiftBinder new (CDelay fc r arg) = CDelay fc r $ shiftBinder new arg
  shiftBinder new (CConCase fc sc alts def)
      = CConCase fc (shiftBinder new sc)
                    (map (shiftBinderConAlt new) alts)
                    (map (shiftBinder new) def)
  shiftBinder new (CConstCase fc sc alts def)
      = CConstCase fc (shiftBinder new sc)
                      (map (shiftBinderConstAlt new) alts)
                      (map (shiftBinder new) def)
  shiftBinder new (CPrimVal fc c) = CPrimVal fc c
  shiftBinder new (CErased fc) = CErased fc
  shiftBinder new (CCrash fc msg) = CCrash fc msg

  shiftBinderConScope : {outer, args : _} ->
                (new : Name) ->
                CCaseScope ((vars ++ args) :< old ++ outer) ->
                CCaseScope ((vars :< new ++ args) ++ outer)
  shiftBinderConScope new (CRHS tm) = CRHS (shiftBinder new tm)
  shiftBinderConScope new (CArg x sc)
      = CArg x (shiftBinderConScope {outer = outer :< x} new sc)

  shiftBinderConAlt : {outer, args : _} ->
                (new : Name) ->
                CConAlt ((vars ++ args) :< old ++ outer) ->
                CConAlt ((vars :< new ++ args) ++ outer)
  shiftBinderConAlt new (MkConAlt n ci t sc)
      = MkConAlt n ci t (shiftBinderConScope new sc)

  shiftBinderConstAlt : {outer, args : _} ->
                (new : Name) ->
                CConstAlt ((vars ++ args) :< old ++ outer) ->
                CConstAlt ((vars :< new ++ args) ++ outer)
  shiftBinderConstAlt new (MkConstAlt c sc) = MkConstAlt c $ shiftBinder new sc

-- If there's a lambda inside a case, move the variable so that it's bound
-- outside the case block so that we can bind it just once outside the block
liftOutLambda : {args : _} ->
                (new : Name) ->
                CExp (vars ++ args :< old) ->
                CExp (vars :< new ++ args)
liftOutLambda = shiftBinder {outer = [<]}

-- If all the alternatives start with a lambda, we can have a single lambda
-- binding outside
tryLiftOut : (new : Name) ->
             List (CConAlt vars) ->
             Maybe (List (CConAlt (vars :< new)))
tryLiftOut new [] = Just []
tryLiftOut new (MkConAlt n ci t sc :: as)
    = do sc' <- tryLiftOutScope {args = [<]} sc
         as' <- tryLiftOut new as
         pure (MkConAlt n ci t sc' :: as')
  where
    tryLiftOutScope : forall vars .
                      {args : _} ->
                      CCaseScope (vars ++ args) ->
                      Maybe (CCaseScope (vars :< new ++ args))
    tryLiftOutScope (CRHS (CLam fc x sc))
        = let sc' = liftOutLambda {args} new sc in
              pure (CRHS sc')
    tryLiftOutScope (CArg x sc)
        = do sc' <- tryLiftOutScope {args = args :< x} sc
             pure (CArg x sc')
    tryLiftOutScope _ = Nothing

tryLiftOutConst : (new : Name) ->
                  List (CConstAlt vars) ->
                  Maybe (List (CConstAlt (vars :< new)))
tryLiftOutConst new [] = Just []
tryLiftOutConst new (MkConstAlt c (CLam fc x sc) :: as)
    = do as' <- tryLiftOutConst new as
         let sc' = liftOutLambda {args = [<]} new sc
         pure (MkConstAlt c sc' :: as')
tryLiftOutConst _ _ = Nothing

tryLiftDef : (new : Name) ->
             Maybe (CExp vars) ->
             Maybe (Maybe (CExp (vars :< new)))
tryLiftDef new Nothing = Just Nothing
tryLiftDef new (Just (CLam fc x sc))
   = let sc' = liftOutLambda {args = [<]} new sc in
         pure (Just sc')
tryLiftDef _ _ = Nothing

allLams : List (CConAlt vars) -> Bool
allLams [] = True
allLams (MkConAlt n ci t sc :: as)
   = if isLam sc
        then allLams as
        else False
  where
    isLam : forall vars . CCaseScope vars -> Bool
    isLam (CRHS (CLam{})) = True
    isLam (CRHS _) = False
    isLam (CArg x sc) = isLam sc

allLamsConst : List (CConstAlt vars) -> Bool
allLamsConst [] = True
allLamsConst (MkConstAlt c (CLam _ _ _) :: as)
   = allLamsConst as
allLamsConst _ = False

-- label for next name for a lambda. These probably don't need really to be
-- unique, since we've proved things about the de Bruijn index, but it's easier
-- to see what's going on if they are.
data NextName : Type where

getName : {auto n : Ref NextName Int} ->
          Core Name
getName
    = do n <- get NextName
         put NextName (n + 1)
         pure (MN "clam" n)

-- The transformation itself
mutual
  caseLam : {auto n : Ref NextName Int} ->
            CExp vars -> Core (CExp vars)
  -- Interesting cases first: look for case blocks where every branch is a
  -- lambda
  caseLam (CConCase fc sc alts def)
      = if allLams alts && defLam def
           then do var <- getName
                   -- These will work if 'allLams' and 'defLam' are consistent.
                   -- We only do that boolean check because it saves us doing
                   -- unnecessary work (say, if the last one we try fails)
                   let Just newAlts = tryLiftOut var alts
                            | Nothing => throw (InternalError "Can't happen caseLam 1")
                   let Just newDef = tryLiftDef var def
                            | Nothing => throw (InternalError "Can't happen caseLam 2")
                   newAlts' <- traverse caseLamConAlt newAlts
                   newDef' <- traverseOpt caseLam newDef
                   -- Q: Should we go around again?
                   pure (CLam fc var (CConCase fc (weaken sc) newAlts' newDef'))
           else do sc' <- caseLam sc
                   alts' <- traverse caseLamConAlt alts
                   def' <- traverseOpt caseLam def
                   pure (CConCase fc sc' alts' def')
    where
      defLam : Maybe (CExp vars) -> Bool
      defLam Nothing = True
      defLam (Just (CLam _ _ _)) = True
      defLam _ = False
  -- Next case is pretty much as above. There's a boring amount of repetition
  -- here because ConstCase is just a little bit different.
  caseLam (CConstCase fc sc alts def)
      = if allLamsConst alts && defLam def
           then do var <- getName
                   -- These will work if 'allLams' and 'defLam' are consistent.
                   -- We only do that boolean check because it saves us doing
                   -- unnecessary work (say, if the last one we try fails)
                   let Just newAlts = tryLiftOutConst var alts
                            | Nothing => throw (InternalError "Can't happen caseLam 1")
                   let Just newDef = tryLiftDef var def
                            | Nothing => throw (InternalError "Can't happen caseLam 2")
                   newAlts' <- traverse caseLamConstAlt newAlts
                   newDef' <- traverseOpt caseLam newDef
                   pure (CLam fc var (CConstCase fc (weaken sc) newAlts' newDef'))
           else do sc' <- caseLam sc
                   alts' <- traverse caseLamConstAlt alts
                   def' <- traverseOpt caseLam def
                   pure (CConstCase fc sc' alts' def')
    where
      defLam : Maybe (CExp vars) -> Bool
      defLam Nothing = True
      defLam (Just (CLam _ _ _)) = True
      defLam _ = False
  -- Structural recursive cases
  caseLam (CLam fc x sc)
      = CLam fc x <$> caseLam sc
  caseLam (CLet fc x inl val sc)
      = CLet fc x inl <$> caseLam val <*> caseLam sc
  caseLam (CApp fc f args)
      = CApp fc <$> caseLam f <*> traverse caseLam args
  caseLam (CCon fc n ci t args)
      = CCon fc n ci t <$> traverse caseLam args
  caseLam (COp fc op args)
      = COp fc op <$> traverseVect caseLam args
  caseLam (CExtPrim fc p args)
      = CExtPrim fc p <$> traverse caseLam args
  caseLam (CForce fc r x)
      = CForce fc r <$> caseLam x
  caseLam (CDelay fc r x)
      = CDelay fc r <$> caseLam x
  -- All the others, no recursive case so just return the input
  caseLam x = pure x

  caseLamConScope : {auto n : Ref NextName Int} ->
                    CCaseScope vars -> Core (CCaseScope vars)
  caseLamConScope (CRHS tm) = CRHS <$> caseLam tm
  caseLamConScope (CArg x sc) = CArg x <$> caseLamConScope sc

  caseLamConAlt : {auto n : Ref NextName Int} ->
                  CConAlt vars -> Core (CConAlt vars)
  caseLamConAlt (MkConAlt n ci tag sc)
      = MkConAlt n ci tag <$> caseLamConScope sc

  caseLamConstAlt : {auto n : Ref NextName Int} ->
                    CConstAlt vars -> Core (CConstAlt vars)
  caseLamConstAlt (MkConstAlt c sc) = MkConstAlt c <$> caseLam sc

export
caseLamDef : {auto c : Ref Ctxt Defs} ->
             Name -> Core ()
caseLamDef n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs) | Nothing => pure ()
         let Just cexpr =  compexpr def             | Nothing => pure ()
         cexpr' <- doCaseLam cexpr
         setCompiled n cexpr'
  where
    doCaseLam : CDef -> Core CDef
    doCaseLam (MkFun args def)
        = do n <- newRef NextName 0
             pure $ MkFun args !(caseLam def)
    doCaseLam d = pure d

{-

Case of case:

case (case x of C1 => E1
                C2 => E2
                ...) of
     D1 => F1
     D2 => F2
     ...
     _ => Fd

can become

case x of
     C1 => case E1 of
                D1 => F1
                D2 => F2
                ...
                _ => Fd
     C2 => case E2 of
                D1 => F1
                D2 => F2
                ...
                _ => Fd

to minimise risk of duplication, do this only when E1, E2 are all
constructor headed, or there's only one branch (for now)

-}

doCaseOfCase : FC ->
               (x : CExp vars) ->
               (xalts : List (CConAlt vars)) ->
               (alts : List (CConAlt vars)) ->
               (def : Maybe (CExp vars)) ->
               CExp vars
doCaseOfCase fc x xalts alts def
    = CConCase fc x (map updateAlt xalts) Nothing
  where
    updateScope : {args : SnocList Name} ->
                  CCaseScope (vars ++ args) -> CCaseScope (vars ++ args)
    updateScope {args} (CRHS tm)
        = CRHS $ CConCase fc tm
                   (map (weakenNs (mkSizeOf args)) alts)
                   (map (weakenNs (mkSizeOf args)) def)
    updateScope (CArg x sc)
        = CArg x (updateScope {args = args :< x} sc)

    updateAlt : CConAlt vars -> CConAlt vars
    updateAlt (MkConAlt n ci t sc)
        = MkConAlt n ci t (updateScope {args = [<]} sc)

doCaseOfConstCase : FC ->
                    (x : CExp vars) ->
                    (xalts : List (CConstAlt vars)) ->
                    (alts : List (CConstAlt vars)) ->
                    (def : Maybe (CExp vars)) ->
                    CExp vars
doCaseOfConstCase fc x xalts alts def
    = CConstCase fc x (map updateAlt xalts) Nothing
  where
    updateAlt : CConstAlt vars -> CConstAlt vars
    updateAlt (MkConstAlt c sc)
        = MkConstAlt c $
              CConstCase fc sc alts def

tryCaseOfCase : CExp vars -> Maybe (CExp vars)
tryCaseOfCase (CConCase fc (CConCase fc' x xalts Nothing) alts def)
    = if canCaseOfCase xalts
         then Just (doCaseOfCase fc' x xalts alts def)
         else Nothing
  where
    conCase : CConAlt vars -> Bool
    conCase (MkConAlt _ _ _ sc) = isCon sc
      where
        isCon : forall vars . CCaseScope vars -> Bool
        isCon (CRHS (CCon _ _ _ _ _)) = True
        isCon (CRHS _) = False
        isCon (CArg x sc) = isCon sc

    canCaseOfCase : List (CConAlt vars) -> Bool
    canCaseOfCase [] = True
    canCaseOfCase [x] = True
    canCaseOfCase xs = all conCase xs
tryCaseOfCase (CConstCase fc (CConstCase fc' x xalts Nothing) alts def)
    = if canCaseOfCase xalts
         then Just (doCaseOfConstCase fc' x xalts alts def)
         else Nothing
  where
    constCase : CConstAlt vars -> Bool
    constCase (MkConstAlt _ (CPrimVal _ _)) = True
    constCase _ = False

    canCaseOfCase : List (CConstAlt vars) -> Bool
    canCaseOfCase [] = True
    canCaseOfCase [x] = True
    canCaseOfCase xs = all constCase xs
tryCaseOfCase _ = Nothing

export
caseOfCase : CExp vars -> CExp vars
caseOfCase tm = go 5 tm
  where
    go : Nat -> CExp vars -> CExp vars
    go Z tm = tm
    go (S k) tm = maybe tm (go k) (tryCaseOfCase tm)
