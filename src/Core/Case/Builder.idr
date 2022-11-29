module Core.Case.Builder

import Core.Case.Patterns
import Core.Case.Util
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Options
import Core.TT
import Core.Evaluate

import Data.List
import Data.SnocList
import Data.String
import Data.Vect
import Libraries.Data.LengthMatch
import Libraries.Data.SortedSet

import Decidable.Equality

import Libraries.Text.PrettyPrint.Prettyprinter


%default covering

%hide Symbols.equals

public export
data Phase = CompileTime RigCount | RunTime

Eq Phase where
  CompileTime r == CompileTime r' = r == r'
  RunTime == RunTime = True
  _ == _ = False

data ArgType : SnocList Name -> Type where
     Known : RigCount -> (ty : Term vars) -> ArgType vars -- arg has type 'ty'
     Stuck : (fty : Term vars) -> ArgType vars
         -- ^ arg will have argument type of 'fty' when we know enough to
         -- calculate it
     Unknown : ArgType vars
         -- arg's type is not yet known due to a previously stuck argument

HasNames (ArgType vars) where

  full gam (Known c ty) = Known c <$> full gam ty
  full gam (Stuck ty) = Stuck <$> full gam ty
  full gam Unknown = pure Unknown

  resolved gam (Known c ty) = Known c <$> resolved gam ty
  resolved gam (Stuck ty) = Stuck <$> resolved gam ty
  resolved gam Unknown = pure Unknown

covering
{ns : _} -> Show (ArgType ns) where
  show (Known c t) = "Known " ++ show c ++ " " ++ show t
  show (Stuck t) = "Stuck " ++ show t
  show Unknown = "Unknown"

record PatInfo (pvar : Name) (vars : SnocList Name) where
  constructor MkInfo
  {idx : Nat}
  {name : Name}
  multiplicity : RigCount -- Cached for using in the 'Case' block
  pat : Pat
  0 loc : IsVar name idx vars
  argType : ArgType vars -- Type of the argument being inspected (i.e.
                         -- *not* refined by this particular pattern)

covering
{vars : _} -> Show (PatInfo n vars) where
  show pi = show (pat pi) ++ " : " ++ show (argType pi)

HasNames (PatInfo n vars) where
  full gam (MkInfo c pat loc argType)
     = do pat <- full gam pat
          argType <- full gam argType
          pure $ MkInfo c pat loc argType

  resolved gam (MkInfo c pat loc argType)
     = do pat <- resolved gam pat
          argType <- resolved gam argType
          pure $ MkInfo c pat loc argType

{-
NamedPats is a list of patterns on the LHS of a clause. Each entry in
the list gives a pattern, and a proof that there is a variable we can
inspect to see if it matches the pattern.

A definition consists of a list of clauses, which are a 'NamedPats' and
a term on the RHS. There is an assumption that corresponding positions in
NamedPats always have the same 'Elem' proof, though this isn't expressed in
a type anywhere.
-}

-- TODO: Switch to SnocList syntax for less confusion
data NamedPats : SnocList Name -> -- pattern variables processed
                 SnocList Name -> -- the pattern variables still to process,
                                  -- in reverse order
                 Type where
     Nil : NamedPats vars [<]
     (::) : PatInfo pvar vars ->
            -- ^ a pattern, where its variable appears in the vars list,
            -- and its type. The type has no variable names; any names it
            -- refers to are explicit
            NamedPats vars ns -> NamedPats vars (ns :< pvar)

getPatInfo : NamedPats vars todo -> List Pat
getPatInfo [] = []
getPatInfo (x :: xs) = pat x :: getPatInfo xs

-- Update the types of patterns based on what we now know about the
-- function type.
-- The 'NF' here is the type of the function defined by the remaining patterns
updatePats : {vars, todo : _} ->
             {auto c : Ref Ctxt Defs} ->
             Env Term vars ->
             NF vars -> NamedPats vars todo -> Core (NamedPats vars todo)
updatePats env nf [] = pure []
updatePats {todo = ns :< pvar} env (VBind fc _ (Pi _ c _ farg) fsc) (p :: ps)
  = case argType p of
         Unknown =>
            do fsc' <- expand !(fsc (vRef fc Bound pvar))
               pure ({ argType := Known c !(quote env farg) } p
                          :: !(updatePats env fsc' ps))
         _ => pure (p :: ps)
updatePats env nf (p :: ps)
  = case argType p of
         Unknown => pure ({ argType := Stuck !(quote env nf) } p :: ps)
         _ => pure (p :: ps)

substInPatInfo : {pvar, vars, todo : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 FC -> Name -> Term vars -> PatInfo pvar vars ->
                 NamedPats vars todo ->
                 Core (PatInfo pvar vars, NamedPats vars todo)
substInPatInfo {pvar} {vars} fc n tm p ps
    = case argType p of
           Known c ty =>
                do tynf <- expand !(nf (mkEnv fc _) ty)
                   case tynf of
                        VApp{} =>
                           pure ({ argType := Known c (substName n tm ty) } p, ps)
                        VMeta{} =>
                           pure ({ argType := Known c (substName n tm ty) } p, ps)
                        VLocal{} =>
                           pure ({ argType := Known c (substName n tm ty) } p, ps)
                        -- Got a concrete type, and that's all we need, so stop
                        _ => pure (p, ps)
           Stuck fty =>
             do let env = mkEnv fc vars
                case !(expand !(nf env (substName n tm fty))) of
                     VBind pfc _ (Pi _ c _ farg) fsc =>
                       do fsc' <- expand !(fsc (vRef pfc Bound pvar))
                          pure ({ argType := Known c !(quote env farg) } p,
                                    !(updatePats env fsc' ps))
                     _ => pure (p, ps)
           Unknown => pure (p, ps)

-- Substitute the name with a term in the pattern types, and reduce further
-- (this aims to resolve any 'Stuck' pattern types)
substInPats : {vars, todo : _} ->
              {auto c : Ref Ctxt Defs} ->
              FC -> Name -> Term vars -> NamedPats vars todo ->
              Core (NamedPats vars todo)
substInPats fc n tm [] = pure []
substInPats fc n tm (p :: ps)
    = do (p', ps') <- substInPatInfo fc n tm p ps
         pure (p' :: !(substInPats fc n tm ps'))

getPat : {idx : Nat} ->
         (0 el : IsVar nm idx ps) -> NamedPats ns ps -> PatInfo nm ns
getPat First (x :: xs) = x
getPat (Later p) (x :: xs) = getPat p xs

dropPat : {idx : Nat} ->
          (0 el : IsVar nm idx ps) ->
          NamedPats ns ps -> NamedPats ns (dropVar ps el)
dropPat First (x :: xs) = xs
dropPat (Later p) (x :: xs) = x :: dropPat p xs

HasNames (NamedPats vars todo) where
  full gam [] = pure []
  full gam (x::xs) = [| (::) (full gam x) (full gam xs) |]

  resolved gam [] = pure []
  resolved gam (x::xs) = [| (::) (resolved gam x) (resolved gam xs) |]

covering
{vars : _} -> {todo : _} -> Show (NamedPats vars todo) where
  show xs = "[" ++ showAll xs ++ "]"
    where
      showAll : {vs, ts : _} -> NamedPats vs ts -> String
      showAll [] = ""
      showAll {ts = _ :< t} [x]
          = show t ++ " " ++ show (pat x) ++ " [" ++ show (argType x) ++ "]"
      showAll {ts = _ :< t} (x :: xs)
          = show t ++ " " ++ show (pat x) ++ " [" ++ show (argType x) ++ "]"
                     ++ ", " ++ showAll xs

Weaken ArgType where
  weaken (Known c ty) = Known c (weaken ty)
  weaken (Stuck fty) = Stuck (weaken fty)
  weaken Unknown = Unknown

  weakenNs s (Known c ty) = Known c (weakenNs s ty)
  weakenNs s (Stuck fty) = Stuck (weakenNs s fty)
  weakenNs s Unknown = Unknown

Weaken (PatInfo p) where
  weaken (MkInfo c p el fty) = MkInfo c p (Later el) (weaken fty)

-- FIXME: perhaps 'vars' should be second argument so we can use Weaken interface
weaken : {x, vars : _} ->
         NamedPats vars todo -> NamedPats (vars :< x) todo
weaken [] = []
weaken (p :: ps) = weaken p :: weaken ps

weakenNs : SizeOf ns ->
           NamedPats vars todo ->
           NamedPats (vars ++ ns) todo
weakenNs ns [] = []
weakenNs ns (p :: ps)
    = weakenNs ns p :: weakenNs ns ps

(++) : NamedPats vars ms -> NamedPats vars ns -> NamedPats vars (ns ++ ms)
(++) [] ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

tail : NamedPats vars (ps :< p) -> NamedPats vars ps
tail (x :: xs) = xs

take : (as : SnocList Name) -> NamedPats vars (bs ++ as) -> NamedPats vars as
take [<] ps = []
take (xs :< x) (p :: ps) = p :: take xs ps

data PatClause : (vars : SnocList Name) -> (todo : SnocList Name) -> Type where
     MkPatClause : List Name -> -- names matched so far (from original lhs)
                                -- TODO: check if we need this!
                   NamedPats vars todo ->
                   Int -> (rhs : Term vars) -> PatClause vars todo

getNPs : PatClause vars todo -> NamedPats vars todo
getNPs (MkPatClause _ lhs pid rhs) = lhs

covering
{vars : _} -> {todo : _} -> Show (PatClause vars todo) where
  show (MkPatClause _ ps pid rhs)
     = show ps ++ " => " ++ show rhs

HasNames (PatClause vars todo) where
  full gam (MkPatClause ns nps i rhs)
     = [| MkPatClause (traverse (full gam) ns) (full gam nps) (pure i) (full gam rhs) |]

  resolved gam (MkPatClause ns nps i rhs)
     = [| MkPatClause (traverse (resolved gam) ns) (resolved gam nps) (pure i) (resolved gam rhs) |]

substInClause : {a, vars, todo : _} ->
                {auto c : Ref Ctxt Defs} ->
                FC -> PatClause vars (todo :< a) ->
                Core (PatClause vars (todo :< a))
substInClause {vars} {a} fc (MkPatClause pvars (MkInfo c pat pprf fty :: pats) pid rhs)
    = do pats' <- substInPats fc a (mkTerm vars pat) pats
         pure (MkPatClause pvars (MkInfo c pat pprf fty :: pats') pid rhs)

data Partitions : List (PatClause vars todo) -> Type where
     ConClauses : {todo, vars, ps : _} ->
                  (cs : List (PatClause vars todo)) ->
                  Partitions ps -> Partitions (cs ++ ps)
     VarClauses : {todo, vars, ps : _} ->
                  (vs : List (PatClause vars todo)) ->
                  Partitions ps -> Partitions (vs ++ ps)
     NoClauses : Partitions []

covering
{ps : _} -> Show (Partitions ps) where
  show (ConClauses cs rest)
    = unlines ("CON" :: map (("  " ++) . show) cs)
    ++ "\n, " ++ show rest
  show (VarClauses vs rest)
    = unlines ("VAR" :: map (("  " ++) . show) vs)
    ++ "\n, " ++ show rest
  show NoClauses = "NONE"

data ClauseType = ConClause | VarClause

namesIn : List Name -> Pat -> Bool
namesIn pvars (PAs _ n p) = (n `elem` pvars) && namesIn pvars p
namesIn pvars (PCon _ _ _ _ ps) = all (namesIn pvars) (map snd ps)
namesIn pvars (PTyCon _ _ _ ps) = all (namesIn pvars) (map snd ps)
namesIn pvars (PArrow _ _ s t) = namesIn pvars s && namesIn pvars t
namesIn pvars (PDelay _ _ t p) = namesIn pvars t && namesIn pvars p
namesIn pvars (PLoc _ n) = n `elem` pvars
namesIn pvars _ = True

namesFrom : Pat -> List Name
namesFrom (PAs _ n p) = n :: namesFrom p
namesFrom (PCon _ _ _ _ ps) = concatMap namesFrom (map snd ps)
namesFrom (PTyCon _ _ _ ps) = concatMap namesFrom (map snd ps)
namesFrom (PArrow _ _ s t) = namesFrom s ++ namesFrom t
namesFrom (PDelay _ _ t p) = namesFrom t ++ namesFrom p
namesFrom (PLoc _ n) = [n]
namesFrom _ = []

clauseType : Phase -> PatClause vars (as :< a) -> ClauseType
-- If it's irrelevant, a constructor, and there's no names we haven't seen yet
-- and don't see later, treat it as a variable
-- Or, if we're compiling for runtime we won't be able to split on it, so
-- also treat it as a variable
-- Or, if it's an under-applied constructor then do NOT attempt to split on it!
clauseType phase (MkPatClause pvars (MkInfo _ arg _ ty :: rest) pid rhs)
    = getClauseType phase arg ty
  where
    -- used when we are tempted to split on a constructor: is
    -- this actually a fully applied one?
    splitCon : Nat -> SnocList (RigCount, Pat) -> ClauseType
    splitCon arity xs
      = if arity == length xs then ConClause else VarClause

    -- used to get the remaining clause types
    clauseType' : Pat -> ClauseType
    clauseType' (PCon _ _ _ a xs) = splitCon a xs
    clauseType' (PTyCon _ _ a xs) = splitCon a xs
    clauseType' (PConst _ x)      = ConClause
    clauseType' (PArrow _ _ s t)  = ConClause
    clauseType' (PDelay _ _ _ _)  = ConClause
    clauseType' _                 = VarClause

    getClauseType : Phase -> Pat -> ArgType vars -> ClauseType
    getClauseType (CompileTime cr) (PCon _ _ _ a xs) (Known r t)
        = if (isErased r && not (isErased cr) &&
             all (namesIn (pvars ++ concatMap namesFrom (getPatInfo rest))) (map snd xs))
             then VarClause
             else splitCon a xs
    getClauseType phase (PAs _ _ p) t = getClauseType phase p t
    getClauseType phase l (Known r t) = if isErased r
      then VarClause
      else clauseType' l
    getClauseType phase l _ = clauseType' l

partition : {a, as, vars : _} ->
            Phase -> (ps : List (PatClause vars (as :< a))) -> Partitions ps
partition phase [] = NoClauses
partition phase (x :: xs) with (partition phase xs)
  partition phase (x :: (cs ++ ps)) | (ConClauses cs rest)
        = case clauseType phase x of
               ConClause => ConClauses (x :: cs) rest
               VarClause => VarClauses [x] (ConClauses cs rest)
  partition phase (x :: (vs ++ ps)) | (VarClauses vs rest)
        = case clauseType phase x of
               ConClause => ConClauses [x] (VarClauses vs rest)
               VarClause => VarClauses (x :: vs) rest
  partition phase (x :: []) | NoClauses
        = case clauseType phase x of
               ConClause => ConClauses [x] NoClauses
               VarClause => VarClauses [x] NoClauses

data ConType : Type where
     CName : Name -> (tag : Int) -> ConType
     CDelay : ConType
     CConst : Constant -> ConType

conTypeEq : (x, y : ConType) -> Maybe (x = y)
conTypeEq (CName x tag) (CName x' tag')
   = do Refl <- nameEq x x'
        case decEq tag tag' of
             Yes Refl => Just Refl
             No contra => Nothing
conTypeEq CDelay CDelay = Just Refl
conTypeEq (CConst x) (CConst y) = cong CConst <$> constantEq x y
conTypeEq _ _ = Nothing

data Group : SnocList Name -> -- variables in scope
             SnocList Name -> -- pattern variables still to process
             Type where
     ConGroup : {newargs : _} ->
                Name -> (tag : Int) ->
                SnocList RigCount -> -- Cached from constructor type
                List (PatClause (vars ++ newargs) (todo ++ newargs)) ->
                Group vars todo
     DelayGroup : {tyarg, valarg : _} ->
                  List (PatClause (vars :< valarg :< tyarg)
                                  (todo :< valarg :< tyarg)) ->
                  Group vars todo
     ConstGroup : Constant -> List (PatClause vars todo) ->
                  Group vars todo

covering
{vars : _} -> {todo : _} -> Show (Group vars todo) where
  show (ConGroup c t _ cs) = "Con " ++ show c ++ ": " ++ show cs
  show (DelayGroup cs) = "Delay: " ++ show cs
  show (ConstGroup c cs) = "Const " ++ show c ++ ": " ++ show cs

data GroupMatch : ConType -> SnocList (RigCount, Pat) -> Group vars todo -> Type where
  ConMatch : {tag : Int} -> LengthMatch ps newargs ->
             GroupMatch (CName n tag) ps
               (ConGroup {newargs} n tag rigs (MkPatClause pvs pats pid rhs :: rest))
  DelayMatch : GroupMatch CDelay [<]
               (DelayGroup {tyarg} {valarg} (MkPatClause pvs pats pid rhs :: rest))
  ConstMatch : GroupMatch (CConst c) [<]
                  (ConstGroup c (MkPatClause pvs pats pid rhs :: rest))
  NoMatch : GroupMatch ct ps g

checkGroupMatch : (c : ConType) -> (ps : SnocList (RigCount, Pat)) -> (g : Group vars todo) ->
                  GroupMatch c ps g
checkGroupMatch (CName x tag) ps (ConGroup {newargs} x' tag' rigs (MkPatClause pvs pats pid rhs :: rest))
    = case checkLengthMatch ps newargs of
           Nothing => NoMatch
           Just prf => case (nameEq x x', decEq tag tag') of
                            (Just Refl, Yes Refl) => ConMatch prf
                            _ => NoMatch
checkGroupMatch (CName x tag) ps _ = NoMatch
checkGroupMatch CDelay [<] (DelayGroup (MkPatClause pvs pats pid rhs :: rest))
    = DelayMatch
checkGroupMatch (CConst c) [<] (ConstGroup c' (MkPatClause pvs pats pid rhs :: rest))
    = case constantEq c c' of
           Nothing => NoMatch
           Just Refl => ConstMatch
checkGroupMatch _ _ _ = NoMatch

data PName : Type where

nextName : {auto i : Ref PName Int} ->
           String -> Core Name
nextName root
    = do x <- get PName
         put PName (x + 1)
         pure (MN root x)

nextNames : {vars : _} ->
            {auto i : Ref PName Int} ->
            {auto c : Ref Ctxt Defs} ->
            FC -> String -> SnocList (RigCount, Pat) -> Maybe (NF vars) ->
            Core (args ** (SizeOf args, NamedPats (vars ++ args) args))
nextNames fc root [<] fty = pure ([<] ** (zero, []))
nextNames {vars} fc root (pats :< (c, p)) fty
     = do defs <- get Ctxt
          n <- nextName root
          let env = mkEnv fc vars
          fa_tys <- the (Core (Maybe (NF vars), ArgType vars)) $
              case fty of
                   Nothing => pure (Nothing, Unknown)
                   Just (VBind pfc _ (Pi _ c _ fargc) fsc) =>
                      do farg <- expand fargc
                         case farg of
                              VErased _ _ =>
                                pure (Just !(expand !(fsc (vRef pfc Bound n))),
                                  Unknown)
                              _ => pure (Just !(expand !(fsc (vRef pfc Bound n))),
                                      Known c !(quote env farg))
                   Just t =>
                      pure (Nothing, Stuck !(quote env t))
          (args ** (l, ps)) <- nextNames {vars} fc root pats (fst fa_tys)
          let argTy = case snd fa_tys of
                           Unknown => Unknown
                           Known rig t => Known rig (weakenNs (suc l) t)
                           Stuck t => Stuck (weakenNs (suc l) t)
          pure (args :< n ** (suc l, MkInfo c p First argTy :: weaken ps))

-- replace the prefix of patterns with 'pargs'
newPats : (pargs : SnocList (RigCount, Pat)) -> LengthMatch pargs ns ->
          NamedPats vars (todo ++ ns) ->
          NamedPats vars ns
newPats [<] LinMatch rest = []
newPats (xs :< (c, newpat)) (SnocMatch w) (pi :: rest)
  = { multiplicity := c,
      pat := newpat } pi :: newPats xs w rest

updateNames : SnocList (Name, Pat) -> SnocList (Name, Name)
updateNames = mapMaybe update
  where
    update : (Name, Pat) -> Maybe (Name, Name)
    update (n, PLoc fc p) = Just (p, n)
    update _ = Nothing

updatePatNames : SnocList (Name, Name) -> NamedPats vars todo -> NamedPats vars todo
updatePatNames _ [] = []
updatePatNames ns (pi :: ps)
    = { pat $= update } pi :: updatePatNames ns ps
  where
    lookup : Name -> SnocList (Name, Name) -> Maybe Name
    lookup n [<] = Nothing
    lookup n (ns :< (x, n')) = if x == n then Just n' else lookup n ns

    update : Pat -> Pat
    update (PAs fc n p)
        = case lookup n ns of
               Nothing => PAs fc n (update p)
               Just n' => PAs fc n' (update p)
    update (PCon fc n i a ps)
        = PCon fc n i a (map (\ (c, t) => (c, update t)) ps)
    update (PTyCon fc n a ps)
        = PTyCon fc n a (map (\ (c, t) => (c, update t)) ps)
    update (PArrow fc x s t) = PArrow fc x (update s) (update t)
    update (PDelay fc r t p) = PDelay fc r (update t) (update p)
    update (PLoc fc n)
        = case lookup n ns of
               Nothing => PLoc fc n
               Just n' => PLoc fc n'
    update p = p

groupCons : {a, vars, todo : _} ->
            {auto i : Ref PName Int} ->
            {auto ct : Ref Ctxt Defs} ->
            FC -> Name ->
            List Name ->
            List (PatClause vars (todo :< a)) ->
            Core (List (Group vars todo))
groupCons fc fn pvars cs
     = gc [] cs
  where
    addConG : {vars', todo' : _} ->
              Name -> (tag : Int) ->
              SnocList (RigCount, Pat) -> NamedPats vars' todo' ->
              Int -> (rhs : Term vars') ->
              (acc : List (Group vars' todo')) ->
              Core (List (Group vars' todo'))
    -- Group all the clauses that begin with the same constructor, and
    -- add new pattern arguments for each of that constructor's arguments.
    -- The type of 'ConGroup' ensures that we refer to the arguments by
    -- the same name in each of the clauses
    addConG {vars'} {todo'} n tag pargs pats pid rhs []
        = do cty <- if n == UN (Basic "->")
                      then pure $ VBind fc (MN "_" 0) (Pi fc top Explicit (VType fc (MN "top" 0))) $
                              (\a => pure $ VBind fc (MN "_" 1) (Pi fc top Explicit (VErased fc Placeholder))
                                (\a => pure $ VType fc (MN "top" 0)))
                      else do defs <- get Ctxt
                              Just t <- lookupTyExact n (gamma defs)
                                   | Nothing => pure (VErased fc Placeholder)
                              expand !(nf (mkEnv fc vars') (embed t))
             (patnames ** (l, newargs)) <- nextNames {vars=vars'} fc "e" pargs (Just cty)
             -- Update non-linear names in remaining patterns (to keep
             -- explicit dependencies in types accurate)
             let pats' = updatePatNames (updateNames (zip patnames (map snd pargs)))
                                        (weakenNs l pats)
             let clause = MkPatClause {todo = todo' ++ patnames}
                              pvars
                              (newargs ++ pats')
                              pid (weakenNs l rhs)
             pure [ConGroup n tag (map fst pargs) [clause]]
    addConG {vars'} {todo'} n tag pargs pats pid rhs (g :: gs) with (checkGroupMatch (CName n tag) pargs g)
      addConG {vars'} {todo'} n tag pargs pats pid rhs
              ((ConGroup {newargs} n tag ms ((MkPatClause pvars ps tid tm) :: rest)) :: gs)
                   | (ConMatch {newargs} lprf)
        = do let newps = newPats pargs lprf ps
             let l = mkSizeOf newargs
             let pats' = updatePatNames (updateNames (zip newargs (map snd pargs)))
                                        (weakenNs l pats)
             let newclause : PatClause (vars' ++ newargs) (todo' ++ newargs)
                   = MkPatClause pvars
                                 (newps ++ pats')
                                 pid
                                 (weakenNs l rhs)
             -- put the new clause at the end of the group, since we
             -- match the clauses top to bottom.
             pure ((ConGroup n tag ms (MkPatClause pvars ps tid tm :: rest ++ [newclause]))
                         :: gs)
      addConG n tag pargs pats pid rhs (g :: gs) | NoMatch
        = do gs' <- addConG n tag pargs pats pid rhs gs
             pure (g :: gs')

    -- This rather ugly special case is to deal with laziness, where Delay
    -- is like a constructor, but with a special meaning that it forces
    -- evaluation when case analysis reaches it (dealt with in the evaluator
    -- and compiler)
    addDelayG : {vars', todo' : _} ->
                Pat -> Pat -> NamedPats vars' todo' ->
                Int -> (rhs : Term vars') ->
                (acc : List (Group vars' todo')) ->
                Core (List (Group vars' todo'))
    addDelayG {vars'} {todo'} pty parg pats pid rhs []
        = do let dty = VBind fc (MN "a" 0) (Pi fc erased Explicit (VType fc (MN "top" 0))) $
                        (\a =>
                            pure (VBind fc (MN "x" 0) (Pi fc top Explicit a)
                                     (\av => pure (VDelayed fc LUnknown a))))
             ([< argname, tyname] ** (l, newargs)) <-
                  nextNames {vars=vars'} fc "e" [< (top, parg), (top, pty)] (Just dty)
                | _ => throw (InternalError "Error compiling Delay pattern match")
             let pats' = updatePatNames (updateNames [< (argname, parg),
                                                        (tyname, pty) ])
                                        (weakenNs l pats)
             let clause = MkPatClause {todo = todo' :< argname :< tyname}
                             pvars (newargs ++ pats')
                                   pid (weakenNs l rhs)
             pure [DelayGroup [clause]]
    addDelayG {vars'} {todo'} pty parg pats pid rhs (g :: gs) with (checkGroupMatch CDelay [<] g)
      addDelayG {vars'} {todo'} pty parg pats pid rhs
          ((DelayGroup {tyarg} {valarg} ((MkPatClause pvars ps tid tm) :: rest)) :: gs)
                 | (DelayMatch {tyarg} {valarg})
         = do let l = mkSizeOf [< valarg, tyarg]
              let newps = newPats [< (top, parg), (top, pty)] (SnocMatch (SnocMatch LinMatch)) ps
              let pats' = updatePatNames (updateNames [< (valarg, parg),
                                                         (tyarg, pty)])
                                         (weakenNs l pats)
              let newclause : PatClause (vars' :< valarg :< tyarg)
                                        (todo' :< valarg :< tyarg)
                    = MkPatClause pvars (newps ++ pats') pid
                                        (weakenNs l rhs)
              pure ((DelayGroup (MkPatClause pvars ps tid tm :: rest ++ [newclause]))
                         :: gs)
      addDelayG pty parg pats pid rhs (g :: gs) | NoMatch
         = do gs' <- addDelayG pty parg pats pid rhs gs
              pure (g :: gs')

    addConstG : {vars', todo' : _} ->
                Constant -> NamedPats vars' todo' ->
                Int -> (rhs : Term vars') ->
                (acc : List (Group vars' todo')) ->
                Core (List (Group vars' todo'))
    addConstG c pats pid rhs []
        = pure [ConstGroup c [MkPatClause pvars pats pid rhs]]
    addConstG {todo'} {vars'} c pats pid rhs (g :: gs) with (checkGroupMatch (CConst c) [<] g)
      addConstG {todo'} {vars'} c pats pid rhs
              ((ConstGroup c ((MkPatClause pvars ps tid tm) :: rest)) :: gs) | ConstMatch
          = let newclause : PatClause vars' todo'
                  = MkPatClause pvars pats pid rhs in
                pure ((ConstGroup c
                      (MkPatClause pvars ps tid tm :: rest ++ [newclause])) :: gs)
      addConstG c pats pid rhs (g :: gs) | NoMatch
          = do gs' <- addConstG c pats pid rhs gs
               pure (g :: gs')

    addGroup : {vars, todo, idx : _} ->
               Pat -> (0 p : IsVar nm idx vars) ->
               NamedPats vars todo -> Int -> Term vars ->
               List (Group vars todo) ->
               Core (List (Group vars todo))
    -- In 'As' replace the name on the RHS with a reference to the
    -- variable we're doing the case split on
    addGroup (PAs fc n p) pprf pats pid rhs acc
         = addGroup p pprf pats pid (substName n (Local fc (Just True) _ pprf) rhs) acc
    addGroup (PCon cfc n t a pargs) pprf pats pid rhs acc
         = if a == length pargs
              then addConG n t pargs pats pid rhs acc
              else throw (CaseCompile cfc fn (NotFullyApplied n))
    addGroup (PTyCon cfc n a pargs) pprf pats pid rhs acc
         = if a == length pargs
           then addConG n 0 pargs pats pid rhs acc
           else throw (CaseCompile cfc fn (NotFullyApplied n))
    addGroup (PArrow _ _ s t) pprf pats pid rhs acc
         = addConG (UN $ Basic "->") 0 [< (top, s), (top, t)] pats pid rhs acc
    -- Go inside the delay; we'll flag the case as needing to force its
    -- scrutinee (need to check in 'caseGroups below)
    addGroup (PDelay _ _ pty parg) pprf pats pid rhs acc
         = addDelayG pty parg pats pid rhs acc
    addGroup (PConst _ c) pprf pats pid rhs acc
         = addConstG c pats pid rhs acc
    addGroup _ pprf pats pid rhs acc = pure acc -- Can't happen, not a constructor
        -- FIXME: Is this possible to rule out with a type? Probably.

    gc : {a, vars, todo : _} ->
         List (Group vars todo) ->
         List (PatClause vars (todo :< a)) ->
         Core (List (Group vars todo))
    gc acc [] = pure acc
    gc {a} acc ((MkPatClause pvars (MkInfo c pat pprf fty :: pats) pid rhs) :: cs)
        = do acc' <- addGroup pat pprf pats pid rhs acc
             gc acc' cs

getFirstPat : NamedPats ns (ps :< p) -> Pat
getFirstPat (p :: _) = pat p

getFirstArgType : NamedPats ns (ps :< p) -> ArgType ns
getFirstArgType (p :: _) = argType p

-- TODO: Idris 2 has an optional heuristic here, but I'm leaving it own
-- for now because it is fiddly to port
nextIdx: {p : _} ->
         {ps : _} ->
         Phase ->
         List (NamedPats ns (ps :< p)) ->
         (n ** NVar n (ps :< p))
nextIdx _ _            = (_ ** (MkNVar First))

-- Check whether all the initial patterns have the same concrete, known
-- and matchable type, which is multiplicity > 0.
-- If so, it's okay to match on it
sameType : {ns : _} ->
           {auto i : Ref PName Int} ->
           {auto c : Ref Ctxt Defs} ->
           FC -> Phase -> Name ->
           Env Term ns -> List (NamedPats ns (ps :< p)) ->
           Core ()
sameType fc phase fn env [] = pure ()
sameType {ns} fc phase fn env (p :: xs)
    = do defs <- get Ctxt
         case getFirstArgType p of
              Known _ t => sameTypeAs phase
                                      !(expand !(nf env t))
                                      (map getFirstArgType xs)
              ty => throw (CaseCompile fc fn DifferingTypes)
  where
    firstPat : NamedPats ns (nps :< np) -> Pat
    firstPat (pinf :: _) = pat pinf

    headEq : NF ns -> NF ns -> Phase -> Bool
    headEq (VBind _ _ (Pi _ _ _ _) _) (VBind _ _ (Pi _ _ _ _) _) _ = True
    headEq (VTCon _ n _ _) (VTCon _ n' _ _) _ = n == n'
    headEq (VPrimVal _ c) (VPrimVal _ c') _ = c == c'
    headEq (VType _ _) (VType _ _) _ = True
    headEq (VApp _ _ n _ _) (VApp _ _ n' _ _) RunTime = n == n'
    headEq (VErased _ _) _ RunTime = True
    headEq _ (VErased _ _) RunTime = True
    headEq _ _ _ = False

    sameTypeAs : Phase -> NF ns -> List (ArgType ns) -> Core ()
    sameTypeAs _ ty [] = pure ()
    sameTypeAs ph ty (Known r t :: xs) =
         do defs <- get Ctxt
            if headEq ty !(expand !(nf env t)) phase
               then sameTypeAs ph ty xs
               else throw (CaseCompile fc fn DifferingTypes)
    sameTypeAs p ty _ = throw (CaseCompile fc fn DifferingTypes)

-- Check whether all the initial patterns are the same, or are all a variable.
-- If so, we'll match it to refine later types and move on
samePat : List (NamedPats ns (ps :< p)) -> Bool
samePat [] = True
samePat (pi :: xs)
    = samePatAs (dropAs (getFirstPat pi))
                        (map (dropAs . getFirstPat) xs)
  where
    dropAs : Pat -> Pat
    dropAs (PAs _ _ p) = p
    dropAs p = p

    samePatAs : Pat -> List Pat -> Bool
    samePatAs p [] = True
    samePatAs (PTyCon fc n a args) (PTyCon _ n' _ _ :: ps)
        = n == n' && samePatAs (PTyCon fc n a args) ps
    samePatAs (PCon fc n t a args) (PCon _ n' t' _ _ :: ps)
        = n == n' && t == t' && samePatAs (PCon fc n t a args) ps
    samePatAs (PConst fc c) (PConst _ c' :: ps)
        = c == c' && samePatAs (PConst fc c) ps
    samePatAs (PArrow fc x s t) (PArrow _ _ s' t' :: ps)
        = samePatAs (PArrow fc x s t) ps
    samePatAs (PDelay fc r t p) (PDelay _ _ _ _ :: ps)
        = samePatAs (PDelay fc r t p) ps
    samePatAs (PLoc fc n) (PLoc _ _ :: ps) = samePatAs (PLoc fc n) ps
    samePatAs x y = False

getFirstCon : NamedPats ns (ps :< p) -> Pat
getFirstCon (p :: _) = pat p

-- Count the number of distinct constructors in the initial pattern
countDiff : List (NamedPats ns (ps :< p)) -> Nat
countDiff xs = length (distinct [] (map getFirstCon xs))
  where
    isVar : Pat -> Bool
    isVar (PAs _ _ p) = isVar p
    isVar (PCon _ _ _ _ _) = False
    isVar (PTyCon _ _ _ _) = False
    isVar (PConst _ _) = False
    isVar (PArrow _ _ _ _) = False
    isVar (PDelay _ _ _ p) = False
    isVar _ = True

    -- Return whether two patterns would lead to the same match
    sameCase : Pat -> Pat -> Bool
    sameCase (PAs _ _ p) p' = sameCase p p'
    sameCase p (PAs _ _ p') = sameCase p p'
    sameCase (PCon _ _ t _ _) (PCon _ _ t' _ _) = t == t'
    sameCase (PTyCon _ t _ _) (PTyCon _ t' _ _) = t == t'
    sameCase (PConst _ c) (PConst _ c') = c == c'
    sameCase (PArrow _ _ _ _) (PArrow _ _ _ _) = True
    sameCase (PDelay _ _ _ _) (PDelay _ _ _ _) = True
    sameCase x y = isVar x && isVar y

    distinct : List Pat -> List Pat -> List Pat
    distinct acc [] = acc
    distinct acc (p :: ps)
       = if elemBy sameCase p acc
            then distinct acc ps
            else distinct (p :: acc) ps

getScore : {ns : _} ->
           {auto i : Ref PName Int} ->
           {auto c : Ref Ctxt Defs} ->
           FC -> Phase -> Name ->
           List (NamedPats ns (ps :< p)) ->
           Core (Either CaseError ())
getScore fc phase name npss
    = do catch (do sameType fc phase name (mkEnv fc ns) npss
                   pure (Right ()))
               $ \case
                 CaseCompile _ _ err => pure $ Left err
                 err => throw err

||| Pick the leftmost matchable thing with all constructors in the
||| same family, or all variables, or all the same type constructor.
pickNextViable : {p, ns, ps : _} ->
           {auto i : Ref PName Int} ->
           {auto c : Ref Ctxt Defs} ->
           FC -> Phase -> Name -> List (NamedPats ns (ps :< p)) ->
           Core (n ** NVar n (ps :< p))
-- last possible variable
pickNextViable {ps = [<]} fc phase fn npss
    = if samePat npss
         then pure (_ ** MkNVar First)
         else do Right () <- getScore fc phase fn npss
                       | Left err => throw (CaseCompile fc fn err)
                 pure (_ ** MkNVar First)
pickNextViable {ps = qs :< q} fc phase fn npss
    = if samePat npss
         then pure (_ ** MkNVar First)
         else  case !(getScore fc phase fn npss) of
                    Right () => pure (_ ** MkNVar First)
                    _ => do (_ ** MkNVar var) <- pickNextViable fc phase fn (map tail npss)
                            pure (_ ** MkNVar (Later var))

moveFirst : {idx : Nat} -> (0 el : IsVar nm idx ps) -> NamedPats ns ps ->
            NamedPats ns (dropVar ps el :< nm)
moveFirst el nps = getPat el nps :: dropPat el nps

shuffleVars : {idx : Nat} -> (0 el : IsVar nm idx todo) -> PatClause vars todo ->
              PatClause vars (dropVar todo el :< nm)
shuffleVars First orig@(MkPatClause pvars lhs pid rhs) = orig -- no-op
shuffleVars el (MkPatClause pvars lhs pid rhs)
    = MkPatClause pvars (moveFirst el lhs) pid rhs

mutual
  {- 'PatClause' contains a list of patterns still to process (that's the
     "todo") and a right hand side with the variables we know about "vars".
     So "match" builds the remainder of the case tree for
     the unprocessed patterns. "err" is the tree for when the patterns don't
     cover the input (i.e. the "fallthrough" pattern, which at the top
     level will be an error). -}
  match : {vars, todo : _} ->
          {auto i : Ref PName Int} ->
          {auto c : Ref Ctxt Defs} ->
          FC -> Name -> Phase ->
          List (PatClause vars todo) -> (err : Maybe (Term vars)) ->
          Core (Term vars)
  -- Before 'partition', reorder the arguments so that the one we
  -- inspect next has a concrete type that is the same in all cases, and
  -- has the most distinct constructors (via pickNextViable)
  match {todo = (_ :< _)} fc fn phase clauses err
      = do let nps = getNPs <$> clauses
           let (_ ** (MkNVar next)) = nextIdx phase nps
           let prioritizedClauses = shuffleVars next <$> clauses
           (n ** MkNVar next') <- pickNextViable fc phase fn (getNPs <$> prioritizedClauses)
           log "compile.casetree.pick" 25 $ "Picked " ++ show n ++ " as the next split"
           let clauses' = shuffleVars next' <$> prioritizedClauses
           log "compile.casetree.clauses" 25 $
             unlines ("Using clauses:" :: map (("  " ++) . show) clauses')
           let ps = partition phase clauses'
           log "compile.casetree.partition" 25 $ "Got Partition:\n" ++ show ps
           mix <- mixture fc fn phase ps err
           case mix of
             Nothing =>
               do log "compile.casetree.intermediate" 25 "match: No clauses"
                  pure (Unmatched fc "No clauses")
             Just m =>
               do log "compile.casetree.intermediate" 25 $ "match: new case tree " ++ show m
                  Core.pure m
  match {todo = [<]} fc fn phase [] err
       = maybe (pure (Unmatched fc "No patterns"))
               pure err
  match {todo = [<]} fc fn phase ((MkPatClause pvars [] pid (Erased _ Impossible)) :: _) err
       = pure (Erased fc Impossible)
  match {todo = [<]} fc fn phase ((MkPatClause pvars [] pid rhs) :: _) err
       = pure rhs

  caseGroups : {pvar, vars, todo : _} ->
               {auto i : Ref PName Int} ->
               {auto c : Ref Ctxt Defs} ->
               FC -> Name -> Phase ->
               RigCount ->
               {idx : Nat} -> (0 p : IsVar pvar idx vars) -> Term vars ->
               List (Group vars todo) -> Maybe (Term vars) ->
               Core (Term vars)
  caseGroups {vars} fc fn phase c el ty gs errorCase
      = do g <- altGroups gs
           pure (Case fc c (Local fc Nothing _ el) (resolveNames vars ty) g)
    where
      mkScope : forall vars . (vs : SnocList Name) ->
                              (ms : SnocList RigCount) ->
                              CaseScope (vars ++ vs) ->
                CaseScope vars
      mkScope [<] _ rhs = rhs
      mkScope (sx :< y) (ms :< c) rhs = mkScope sx ms (Arg c y rhs)
      mkScope (sx :< y) _ rhs = mkScope sx [<] (Arg top y rhs)

      altGroups : List (Group vars todo) -> Core (List (CaseAlt vars))
      altGroups [] = maybe (pure [])
                           (\e => pure [DefaultCase fc e])
                           errorCase
      altGroups (ConGroup {newargs} cn tag ms rest :: cs)
          = do crest <- match fc fn phase rest (map (weakenNs (mkSizeOf newargs)) errorCase)
               cs' <- altGroups cs
               pure (ConCase fc cn tag (mkScope newargs ms (RHS crest)) :: cs')
      altGroups (DelayGroup {tyarg} {valarg} rest :: cs)
          = do crest <- match fc fn phase rest
                             (map (weakenNs (mkSizeOf [< valarg, tyarg])) errorCase)
               cs' <- altGroups cs
               pure (DelayCase fc tyarg valarg crest :: cs')
      altGroups (ConstGroup c rest :: cs)
          = do crest <- match fc fn phase rest errorCase
               cs' <- altGroups cs
               pure (ConstCase fc c crest :: cs')

  conRule : {a, vars, todo : _} ->
            {auto i : Ref PName Int} ->
            {auto c : Ref Ctxt Defs} ->
            FC -> Name -> Phase ->
            List (PatClause vars (todo :< a)) ->
            Maybe (Term vars) ->
            Core (Term vars)
  conRule fc fn phase [] err = maybe (pure (Unmatched fc "No constructor clauses")) pure err
  -- ASSUMPTION, not expressed in the type, that the patterns all have
  -- the same variable (pprf) for the first argument. If not, the result
  -- will be a broken case tree... so we should find a way to express this
  -- in the type if we can.
  conRule {a} fc fn phase cs@(MkPatClause pvars (MkInfo c pat pprf fty :: pats) pid rhs :: rest) err
      = do refinedcs <- traverse (substInClause fc) cs
           groups <- groupCons fc fn pvars refinedcs
           ty <- case fty of
                      Known _ t => pure t
                      _ => throw (CaseCompile fc fn UnknownType)
           caseGroups fc fn phase c pprf ty groups err

  varRule : {a, vars, todo : _} ->
            {auto i : Ref PName Int} ->
            {auto c : Ref Ctxt Defs} ->
            FC -> Name -> Phase ->
            List (PatClause vars (todo :< a)) ->
            Maybe (Term vars) ->
            Core (Term vars)
  varRule {vars} {a} fc fn phase cs err
      = do alts' <- traverse updateVar cs
           match fc fn phase alts' err
    where
      updateVar : PatClause vars (todo :< a) -> Core (PatClause vars todo)
      -- replace the name with the relevant variable on the rhs
      updateVar (MkPatClause pvars (MkInfo c (PLoc pfc n) prf fty :: pats) pid rhs)
          = pure $ MkPatClause (n :: pvars)
                        !(substInPats fc a (Local pfc (Just False) _ prf) pats)
                        pid (substName n (Local pfc (Just False) _ prf) rhs)
      -- If it's an as pattern, replace the name with the relevant variable on
      -- the rhs then continue with the inner pattern
      updateVar (MkPatClause pvars (MkInfo c (PAs pfc n pat) prf fty :: pats) pid rhs)
          = do pats' <- substInPats fc a (mkTerm _ pat) pats
               let rhs' = substName n (Local pfc (Just True) _ prf) rhs
               updateVar (MkPatClause pvars (MkInfo c pat prf fty :: pats') pid rhs')
      -- match anything, name won't appear in rhs but need to update
      -- LHS pattern types based on what we've learned
      updateVar (MkPatClause pvars (MkInfo c pat prf fty :: pats) pid rhs)
          = pure $ MkPatClause pvars
                        !(substInPats fc a (mkTerm vars pat) pats) pid rhs

  mixture : {a, vars, todo : _} ->
            {auto i : Ref PName Int} ->
            {auto c : Ref Ctxt Defs} ->
            {ps : List (PatClause vars (todo :< a))} ->
            FC -> Name -> Phase ->
            Partitions ps ->
            Maybe (Term vars) ->
            Core (Maybe (Term vars))
  mixture fc fn phase (ConClauses cs rest) err
      = do fallthrough <- mixture fc fn phase rest err
           pure (Just !(conRule fc fn phase cs fallthrough))
  mixture fc fn phase (VarClauses vs rest) err
      = do fallthrough <- mixture fc fn phase rest err
           pure (Just !(varRule fc fn phase vs fallthrough))
  mixture fc fn {a} {todo} phase NoClauses err
      = pure err

export
mkPat : {auto c : Ref Ctxt Defs} -> SnocList (RigCount, Pat) -> ClosedTerm -> ClosedTerm -> Core Pat
mkPat args orig (Ref fc Bound n) = pure $ PLoc fc n
mkPat args orig (Ref fc (DataCon t a) n) = pure $ PCon fc n t a (reverse args)
mkPat args orig (Ref fc (TyCon a) n) = pure $ PTyCon fc n a (reverse args)
mkPat args orig (Ref fc Func n)
  = do prims <- getPrimitiveNames
       mtm <- normalisePrims (const True) isPConst True prims n (map snd args) orig [<]
       case mtm of
         Just tm => if tm /= orig -- check we made progress; if there's an
                                  -- unresolved interface, we might be stuck
                                  -- and we'd loop forever
                       then mkPat [<] tm tm
                       else -- Possibly this should be an error instead?
                            pure $ PUnmatchable (getLoc orig) orig
         Nothing =>
           do log "compile.casetree" 10 $
                "Unmatchable function: " ++ show n
              pure $ PUnmatchable (getLoc orig) orig
mkPat args orig (Bind fc x (Pi _ _ _ s) t)
    = let t' = subst (Erased fc Placeholder) t in
      pure $ PArrow fc x !(mkPat [<] s s) !(mkPat [<] t' t')
mkPat args orig (App fc fn c arg)
    = do parg <- mkPat [<] arg arg
         mkPat (args :< (c, parg)) orig fn
-- Assumption is that clauses are converted to explicit names
mkPat args orig (As fc _ (Ref _ Bound n) ptm)
    = pure $ PAs fc n !(mkPat [<] ptm ptm)
mkPat args orig (As fc _ _ ptm)
    = mkPat [<] orig ptm
mkPat args orig (TDelay fc r ty p)
    = pure $ PDelay fc r !(mkPat [<] orig ty) !(mkPat [<] orig p)
mkPat args orig (PrimVal fc $ PrT c) -- Primitive type constant
    = pure $ PTyCon fc (UN (Basic $ show c)) 0 [<]
mkPat args orig (PrimVal fc c) = pure $ PConst fc c -- Non-type constant
mkPat args orig (TType fc _) = pure $ PTyCon fc (UN $ Basic "Type") 0 [<]
mkPat args orig tm
   = do log "compile.casetree" 10 $
          "Catchall: marking " ++ show tm ++ " as unmatchable"
        pure $ PUnmatchable (getLoc orig) orig

export
argToPat : {auto c : Ref Ctxt Defs} -> (RigCount, ClosedTerm) -> Core (Pat, RigCount)
argToPat (c, tm) = pure (!(mkPat [<] tm tm), c)

mkPatClause : {auto c : Ref Ctxt Defs} ->
              FC -> Name ->
              (args : SnocList Name) -> ClosedTerm ->
              Int -> (SnocList (Pat, RigCount), ClosedTerm) ->
              Core (PatClause args args)
mkPatClause fc fn args ty pid (ps, rhs)
    = maybe (throw (CaseCompile fc fn DifferingArgNumbers))
            (\eq =>
               do nty <- expand !(nf [<] ty)
                  -- The arguments are in reverse order, so we need to
                  -- read what we know off 'nty' then reverse it
                  argTys <- getArgTys (cast args) nty
                  ns <- mkNames args ps eq (reverse argTys)
                  log "compile.casetree" 20 $
                    "Make pat clause for names " ++ show ns
                     ++ " in LHS " ++ show ps
                  pure (MkPatClause [] ns pid
                          (rewrite sym (appendLinLeftNeutral args) in
                                   (weakenNs (mkSizeOf args) rhs))))
            (checkLengthMatch args ps)
  where
    getArgTys : List Name -> NF [<] -> Core (List (ArgType [<]))
    getArgTys (n :: ns) (VBind pfc _ (Pi _ c _ farg) fsc)
        = do rest <- getArgTys ns !(expand !(fsc (vRef pfc Bound n)))
             pure (Known c !(quote [<] farg) :: rest)
    getArgTys (n :: ns) t
        = pure [Stuck !(quote [<] t)]
    getArgTys _ _ = pure []

    mkNames : (vars : SnocList Name) -> (ps : SnocList (Pat, RigCount)) ->
              LengthMatch vars ps -> List (ArgType [<]) ->
              Core (NamedPats vars vars)
    mkNames [<] [<] LinMatch fty = pure []
    mkNames (args :< arg) (ps :< (p, pc)) (SnocMatch eq) []
        = do rest <- mkNames args ps eq []
             pure (MkInfo pc p First Unknown :: weaken rest)
    mkNames (args :< arg) (ps :< (p, pc)) (SnocMatch eq) (f :: fs)
        = do rest <- mkNames args ps eq fs
             pure (MkInfo pc p First (embed f) :: weaken rest)
      where
        embed : ArgType [<] -> ArgType more
        embed Unknown = Unknown
        embed (Stuck t) = Stuck (TT.embed {more} t)
        embed (Known c t) = Known c (TT.embed {more} t)

export
patCompile : {auto c : Ref Ctxt Defs} ->
             FC -> Name -> Phase ->
             ClosedTerm -> List (SnocList (Pat, RigCount), ClosedTerm) ->
             Maybe ClosedTerm ->
             Core (args ** Term args)
patCompile fc fn phase ty [] def
    = maybe (pure ([<] ** Unmatched fc "No definition"))
            (\e => pure ([<] ** e))
            def
patCompile fc fn phase ty (p :: ps) def
    = do let (ns ** num) = getNames 0 (fst p)
         pats <- mkPatClausesFrom 0 ns (p :: ps)
         -- higher verbosity: dump the raw data structure
         log "compile.casetree" 10 $ show pats
         i <- newRef PName (the Int 0)
         cases <- match fc fn phase pats
                        (rewrite sym (appendLinLeftNeutral ns) in
                                 map (TT.weakenNs num) def)
         pure (_ ** cases)
  where
    mkPatClausesFrom : Int -> (args : SnocList Name) ->
                       List (SnocList (Pat, RigCount), ClosedTerm) ->
                       Core (List (PatClause args args))
    mkPatClausesFrom i ns [] = pure []
    mkPatClausesFrom i ns (p :: ps)
        = do p' <- mkPatClause fc fn ns ty i p
             ps' <- mkPatClausesFrom (i + 1) ns ps
             pure (p' :: ps')

    getNames : Int -> SnocList (Pat, RigCount) -> (ns : SnocList Name ** SizeOf ns)
    getNames i [<] = ([<] ** zero)
    getNames i (xs :< x) =
      let (ns ** n) = getNames (i + 1) xs
      in (ns :< MN "arg" i ** suc n)

toPatClause : {auto c : Ref Ctxt Defs} ->
              FC -> Name -> (ClosedTerm, ClosedTerm) ->
              Core (SnocList (Pat, RigCount), ClosedTerm)
toPatClause fc n (lhs, rhs)
    = case getFnArgsSpine lhs of
           (Ref ffc Func fn, args)
              => do defs <- get Ctxt
                    (np, _) <- getPosition n (gamma defs)
                    (fnp, _) <- getPosition fn (gamma defs)
                    if np == fnp
                       then pure (!(traverseSnocList argToPat args), rhs)
                       else throw (GenericMsg ffc ("Wrong function name in pattern LHS " ++ show (n, fn)))
           (f, args) => throw (GenericMsg fc "Not a function name in pattern LHS")

-- Assumption (given 'ClosedTerm') is that the pattern variables are
-- explicitly named. We'll assign de Bruijn indices when we're done, and
-- the names of the top level variables we created are returned in 'args'
export
simpleCase : {auto c : Ref Ctxt Defs} ->
             FC -> Phase -> Name -> ClosedTerm -> (def : Maybe ClosedTerm) ->
             (clauses : List (ClosedTerm, ClosedTerm)) ->
             Core (args ** Term args)
simpleCase fc phase fn ty def clauses
    = do ps <- traverse (toPatClause fc fn) clauses
         patCompile fc fn phase ty ps def

mutual
  findCaseLeafAlts : CaseAlt ns -> List FC
  findCaseLeafAlts (ConCase _ _ _ t) = findCaseLeafScope t
  findCaseLeafAlts (DelayCase _ _ _ t) = findCaseLeaf t
  findCaseLeafAlts (ConstCase _ _ t) = findCaseLeaf t
  findCaseLeafAlts (DefaultCase _ t) = findCaseLeaf t

  findCaseLeafScope : CaseScope ns -> List FC
  findCaseLeafScope (RHS tm) = findCaseLeaf tm
  findCaseLeafScope (Arg _ _ sc) = findCaseLeafScope sc

  -- Find the locations of all the leaves of the case tree, so that we can
  -- later work out which ones are reachable
  findCaseLeaf : Term ns -> List FC
  findCaseLeaf (Case _ _ _ _ alts) = concatMap findCaseLeafAlts alts
  findCaseLeaf tm = [getLoc tm]

-- Replace a default case with explicit branches for the constructors.
-- This is easier than checking whether a default is needed when traversing
-- the tree (just one constructor lookup up front).
-- Unreachable defaults are those that when replaced by all possible constructors
-- followed by a removal of duplicate cases there is one _fewer_ total case alts.
identifyUnreachableDefaults : {auto c : Ref Ctxt Defs} ->
                              {vars : _} ->
                              FC -> NF vars -> List (CaseAlt vars) ->
                              Core (SortedSet FC)
-- Leave it alone if it's a primitive type though, since we need the catch
-- all case there
identifyUnreachableDefaults fc (VPrimVal _ _) cs = pure empty
identifyUnreachableDefaults fc (VType _ _) cs = pure empty
identifyUnreachableDefaults fc nfty cs
    = do cs' <- traverse rep cs
         let (cs'', extraClauseIdxs) = dropRep (concat cs') empty
         let extraClauseIdxs' =
           if (length cs == (length cs'' + 1))
              then extraClauseIdxs
              else empty
         -- if a clause is unreachable under all the branches it can be found under
         -- then it is entirely unreachable.
         when (not $ null extraClauseIdxs') $
           log "compile.casetree.clauses" 25 $
             "Marking the following clause indices as unreachable under the current branch of the tree: " ++ (show extraClauseIdxs')
         pure extraClauseIdxs'
  where
    rep : CaseAlt vars -> Core (List (CaseAlt vars))
    rep (DefaultCase _ sc)
        = do defs <- get Ctxt
             allCons <- getCons defs nfty
             pure (map (mkAlt fc sc) allCons)
    rep c = pure [c]

    dropRep : List (CaseAlt vars) -> SortedSet FC ->
              (List (CaseAlt vars), SortedSet FC)
    dropRep [] extra = ([], extra)
    dropRep (c@(ConCase _ n t sc) :: rest) extra
          -- assumption is that there's no defaultcase in 'rest' because
          -- we've just removed it
        = let (filteredClauses, extraCases) = partition (not . tagIs t) rest
              extraClauses = extraCases >>= findCaseLeafAlts
              (rest', extra') = dropRep filteredClauses $ fromList extraClauses
          in  (c :: rest', extra `union` extra')
    dropRep (c :: rest) extra
        = let (rest', extra') = dropRep rest extra
          in  (c :: rest', extra')

||| Find unreachable default paths through the tree for each clause.
||| This is accomplished by expanding default clauses into all concrete constructions
||| and then listing the clauses reached.
||| We identify clauses by their source location (so assume that they arise
||| from an actual source file, not an EmptyFC)
||| This list of clauses can be substracted from the list of "reachable" clauses
||| and if it turns out that the number of unreachable ways to use a clause is equal
||| to the number of ways to reach a RHS for that clause then the clause is totally
||| superfluous (it will never be reached).
findExtraDefaults : {auto c : Ref Ctxt Defs} ->
                   {vars : _} ->
                   Term vars -> Core (List FC)
findExtraDefaults ctree@(Case fc c sc scty altsIn)
  = do let fenv = mkEnv fc _
       nfty <- expand !(nf fenv scty)
       extraCases <- identifyUnreachableDefaults fc nfty altsIn
       extraCases' <- concat <$> traverse findExtraAlts altsIn
       pure (SortedSet.toList extraCases ++ extraCases')
  where
    findExtraAltsScope : {vars : _} -> CaseScope vars -> Core (List FC)
    findExtraAltsScope (RHS tm) = findExtraDefaults tm
    findExtraAltsScope (Arg c x sc) = findExtraAltsScope sc

    findExtraAlts : CaseAlt vars -> Core (List FC)
    findExtraAlts (ConCase fc x tag sc) = findExtraAltsScope sc
    findExtraAlts (DelayCase fc x arg ctree') = findExtraDefaults ctree'
    findExtraAlts (ConstCase fc x ctree') = findExtraDefaults ctree'
    -- already handled defaults by elaborating them to all possible cons
    findExtraAlts (DefaultCase fc ctree') = pure []

findExtraDefaults ctree = pure []

-- Returns the case tree under the yet-to-be-bound lambdas,
-- and a list of the clauses that aren't reachable
makePMDef : {auto c : Ref Ctxt Defs} ->
            FC -> Phase -> Name -> ClosedTerm -> List Clause ->
            Core (args ** (Term args, List Clause))
-- If there's no clauses, make a definition with the right number of arguments
-- for the type, which we can use in coverage checking to ensure that one of
-- the arguments has an empty type
makePMDef fc phase fn ty []
    = do log "compile.casetree.getpmdef" 20 "getPMDef: No clauses!"
         defs <- get Ctxt
         pure (!(getArgs 0 !(expand !(nf [<] ty))) ** (Unmatched fc "No clauses", []))
  where
    getArgs : Int -> NF [<] -> Core (SnocList Name)
    getArgs i (VBind fc x (Pi _ _ _ _) sc)
        = do defs <- get Ctxt
             sc' <- expand !(sc (VErased fc Placeholder))
             pure (!(getArgs i sc') :< MN "arg" i)
    getArgs i _ = pure [<]
makePMDef fc phase fn ty clauses
    = do let cs = map toClosed (labelPat 0 clauses)
         (_ ** t) <- simpleCase fc phase fn ty Nothing cs
         logC "compile.casetree.getpmdef" 20 $
           pure $ "Compiled to: " ++ show !(toFullNames t)
         let allRHS = findCaseLeaf t
         log "compile.casetree.clauses" 25 $
           "All RHSes: " ++ (show allRHS)
         extraDefaults <- findExtraDefaults t
         let unreachable = getUnreachable (allRHS \\ extraDefaults) clauses
         pure (_ ** (t, unreachable))
  where
    getUnreachable : List FC -> List Clause -> List Clause
    getUnreachable is [] = []
    getUnreachable is (c@(MkClause _ _ rhs) :: cs)
        = if getLoc rhs `elem` is
             then getUnreachable is cs
             else c :: getUnreachable is cs

    labelPat : Int -> List a -> List (String, a)
    labelPat i [] = []
    labelPat i (x :: xs) = ("pat" ++ show i ++ ":", x) :: labelPat (i + 1) xs

    mkSubstEnv : Int -> String -> Env Term vars -> SubstEnv vars [<]
    mkSubstEnv i pname [<] = Lin
    mkSubstEnv i pname (vs :< v)
       = mkSubstEnv (i + 1) pname vs :< Ref fc Bound (MN pname i)

    close : {vars : _} ->
            Env Term vars -> String -> Term vars -> ClosedTerm
    close {vars} env pname tm
        = substs (mkSubstEnv 0 pname env)
              (rewrite appendLinLeftNeutral vars in tm)

    toClosed :  (String, Clause) -> (ClosedTerm, ClosedTerm)
    toClosed  (pname, MkClause env lhs rhs)
          = (close env pname lhs, close env pname rhs)

-- Returns the case tree, and a list of the clauses that aren't reachable
export
getPMDef : {auto c : Ref Ctxt Defs} ->
           FC -> Phase -> Name -> ClosedTerm -> List Clause ->
           Core (ClosedTerm, List Clause)
getPMDef fc p n ty cs
    = do (args ** (tree, missing)) <- makePMDef fc p n ty cs
         -- We need to bind lambdas, and we can only do that if we know
         -- the types of the function arguments, so normalise the type just
         -- enough to get that
--          nty <- normaliseBinders [<] ty
--          let (tyargs ** env) = mkEnv [<] nty
--          let Just lenOK = areVarsCompatible args tyargs
         let tm = bindLams _ tree
--              | Nothing => throw (CaseCompile fc n CantResolveType)
         pure (tm, missing)
   where
     mkEnv : {vars : _} -> Env Term vars -> Term vars ->
             (args ** Env Term args)
     mkEnv env (Bind _ x b@(Pi pfc c p ty) sc) = mkEnv (env :< b) sc
     mkEnv env tm = (_ ** env)

     bindLams : (args' : _) ->
                Term args' -> Term [<]
     bindLams [<] tree = tree
     bindLams (as :< a) tree
         = bindLams as (Bind fc _
                           (Lam fc top
                                Explicit
                                (Erased fc Placeholder)) tree)
