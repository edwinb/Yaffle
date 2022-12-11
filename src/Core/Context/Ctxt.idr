module Core.Context.Ctxt

-- This module includes:
-- * Looking up values in the context

-- Context entries read from TTC files will be stored as Binary, so when
-- we look them up, we have to decode them

import Core.Binary
import Core.CompileExpr
import public Core.Context.CtxtData
import public Core.Context.Def
import Core.Error
import Core.Hash
import Core.Options
import Core.TT

import Data.IORef
import Data.Maybe

import Libraries.Data.IntMap
import Libraries.Data.IOArray
import Libraries.Data.NameMap
import Libraries.Data.StringMap
import Libraries.Data.UserNameMap

import Libraries.Utils.Scheme

initSize : Int
initSize = 10000

Grow : Int
Grow = initSize

export
initCtxtS : Int -> CoreE err Context
initCtxtS s
    = do arr <- coreLift $ newArray s
         aref <- newRef Arr arr
         pure $ MkContext
            { firstEntry = 0
            , nextEntry = 0
            , stringTable = stInit
            , resolvedAs = empty
            , possibles = empty
            , content = aref
            , branchDepth = 0
            , staging = empty
            , visibleNS = [partialEvalNS]
            , allPublic = False
            , inlineOnly = False
            , hidden = empty
            }

export
initCtxt : CoreE err Context
initCtxt = initCtxtS initSize

addPossible : Name -> Int ->
              UserNameMap (List PossibleName) -> UserNameMap (List PossibleName)
addPossible n i ps
    = case userNameRoot n of
           Nothing => ps
           Just nr =>
              case lookup nr ps of
                   Nothing => insert nr [Direct n i] ps
                   Just nis => insert nr (Direct n i :: nis) ps

addAlias : Name -> Name -> Int ->
           UserNameMap (List PossibleName) -> UserNameMap (List PossibleName)
addAlias alias full i ps
    = case userNameRoot alias of
           Nothing => ps
           Just nr =>
              case lookup nr ps of
                   Nothing => insert nr [Alias alias full i] ps
                   Just nis => insert nr (Alias alias full i :: nis) ps

export
newEntry : Name -> Context -> CoreE err (Int, Context)
newEntry n ctxt
    = do let idx = nextEntry ctxt
         let a = content ctxt
         arr <- get Arr
         when (idx >= max arr) $
                 do arr' <- coreLift $ newArrayCopy (max arr + Grow) arr
                    put Arr arr'
         pure (idx, { nextEntry := idx + 1,
                      resolvedAs $= insert n idx,
                      possibles $= addPossible n idx
                    } ctxt)

-- Get the position of the next entry in the context array, growing the
-- array if it's out of bounds.
-- Updates the context with the mapping from name to index
export
getPosition : Name -> Context -> CoreE err (Int, Context)
getPosition (Resolved idx) ctxt = pure (idx, ctxt)
getPosition n ctxt
    = case lookup n (resolvedAs ctxt) of
           Just idx =>
              do pure (idx, ctxt)
           Nothing => newEntry n ctxt

export
newAlias : Name -> Name -> Context -> CoreE err Context
newAlias alias full ctxt
    = do (idx, ctxt) <- getPosition full ctxt
         pure $ { possibles $= addAlias alias full idx } ctxt

export
getNameID : Name -> Context -> Maybe Int
getNameID (Resolved idx) ctxt = Just idx
getNameID n ctxt = lookup n (resolvedAs ctxt)

-- Add the name to the context, or update the existing entry if it's already
-- there.
-- If we're not at the top level, add it to the staging area
export
addCtxt : Name -> GlobalDef -> Context -> CoreE err (Int, Context)
addCtxt n val ctxt_in
    = if branchDepth ctxt_in == 0
         then do (idx, ctxt) <- getPosition n ctxt_in
                 let a = content ctxt
                 arr <- get Arr
                 coreLift $ writeArray arr idx (Decoded val)
                 pure (idx, ctxt)
         else do (idx, ctxt) <- getPosition n ctxt_in
                 pure (idx, { staging $= insert idx (Decoded val) } ctxt)

-- Add a context entry directly (that is, a thing that might be a definition
-- or a binary blob, probably that we've just read from a TTC)
export
addEntry : Name -> ContextEntry -> Context -> CoreE err (Int, Context)
addEntry n entry ctxt_in
    = if branchDepth ctxt_in == 0
         then do (idx, ctxt) <- getPosition n ctxt_in
                 let a = content ctxt
                 arr <- get Arr
                 coreLift $ writeArray arr idx entry
                 pure (idx, ctxt)
         else do (idx, ctxt) <- getPosition n ctxt_in
                 pure (idx, { staging $= insert idx entry } ctxt)

export
getContent : Context -> Ref Arr (IOArray ContextEntry)
getContent = content

-- Needs HasNames and TTC instances, so defined in Core.TTC
export
decode : Context -> Int -> (update : Bool) -> ContextEntry ->
         Core GlobalDef

returnDef : Bool -> Int -> GlobalDef -> Maybe (Int, GlobalDef)
returnDef False idx def = Just (idx, def)
returnDef True idx def
    = case definition def of
           Function pi _ _ _ =>
                 if alwaysReduce pi
                    then Just (idx, def)
                    else Nothing
           _ => Nothing

export
lookupCtxtExactI : Name -> Context -> Core (Maybe (Int, GlobalDef))
lookupCtxtExactI (Resolved idx) ctxt
    = case lookup idx (staging ctxt) of
           Just val =>
                pure $ returnDef (inlineOnly ctxt) idx
                                 !(decode ctxt idx True val)
           Nothing =>
              do arr <- get Arr @{content ctxt}
                 Just def <- coreLift (readArray arr idx)
                      | Nothing => pure Nothing
                 pure $ returnDef (inlineOnly ctxt) idx
                                  !(decode ctxt idx True def)
lookupCtxtExactI n ctxt
    = do let Just idx = lookup n (resolvedAs ctxt)
                  | Nothing => pure Nothing
         lookupCtxtExactI (Resolved idx) ctxt

export
lookupCtxtExact : Name -> Context -> Core (Maybe GlobalDef)
lookupCtxtExact (Resolved idx) ctxt
    = case lookup idx (staging ctxt) of
           Just res =>
                do def <- decode ctxt idx True res
                   pure $ map (\(_, def) => def) $
                     returnDef (inlineOnly ctxt) idx def
           Nothing =>
              do arr <- get Arr @{content ctxt}
                 Just res <- coreLift (readArray arr idx)
                      | Nothing => pure Nothing
                 def <- decode ctxt idx True res
                 pure $ map (\(_, def) => def) $
                   returnDef (inlineOnly ctxt) idx def
lookupCtxtExact n ctxt
    = do Just (i, def) <- lookupCtxtExactI n ctxt
              | Nothing => pure Nothing
         pure (Just def)

export
lookupContextEntry : Name -> Context -> Core (Maybe (Int, ContextEntry))
lookupContextEntry (Resolved idx) ctxt
    = case lookup idx (staging ctxt) of
           Just res => pure (Just (idx, res))
           Nothing =>
              do let a = content ctxt
                 arr <- get Arr
                 Just res <- coreLift (readArray arr idx)
                      | Nothing => pure Nothing
                 pure (Just (idx, res))
lookupContextEntry n ctxt
    = do let Just idx = lookup n (resolvedAs ctxt)
                  | Nothing => pure Nothing
         lookupContextEntry (Resolved idx) ctxt

||| Check if the given name has been hidden by the `%hide` directive.
export
isHidden : Name -> Context -> Bool
isHidden fulln ctxt = isJust $ lookup fulln (hidden ctxt)

||| Look up a possibly hidden name in the context. The first (boolean) argument
||| controls whether names hidden by `%hide` are returned too (True=yes, False=no).
export
lookupCtxtName' : Bool -> Name -> Context -> Core (List (Name, Int, GlobalDef))
lookupCtxtName' allowHidden n ctxt
    = case userNameRoot n of
           Nothing => do Just (i, res) <- lookupCtxtExactI n ctxt
                              | Nothing => pure []
                         pure [(n, i, res)]
           Just r =>
              do let Just ps = lookup r (possibles ctxt)
                      | Nothing => pure []
                 lookupPossibles [] ps
  where

    resn : (Name, Int, GlobalDef) -> Int
    resn (_, i, _) = i

    hlookup : Name -> NameMap () -> Maybe ()
    hlookup fulln hiddens = if allowHidden
      then Nothing
      else lookup fulln hiddens

    lookupPossibles : List (Name, Int, GlobalDef) -> -- accumulator
                      List PossibleName ->
                      Core (List (Name, Int, GlobalDef))
    lookupPossibles acc [] = pure (reverse acc)
    lookupPossibles acc (Direct fulln i :: ps)
       = case (hlookup fulln (hidden ctxt)) of
              Nothing =>
                do Just res <- lookupCtxtExact (Resolved i) ctxt
                        | Nothing => lookupPossibles acc ps
                   if matches n fulln && not (i `elem` map resn acc)
                      then lookupPossibles ((fulln, i, res) :: acc) ps
                      else lookupPossibles acc ps
              _ => lookupPossibles acc ps
    lookupPossibles acc (Alias asn fulln i :: ps)
       = case (hlookup fulln (hidden ctxt)) of
              Nothing =>
                do Just res <- lookupCtxtExact (Resolved i) ctxt
                        | Nothing => lookupPossibles acc ps
                   if (matches n asn) && not (i `elem` map resn acc)
                      then lookupPossibles ((fulln, i, res) :: acc) ps
                      else lookupPossibles acc ps
              _ => lookupPossibles acc ps

||| Look up a name in the context, ignoring names hidden by `%hide`.
export
lookupCtxtName : Name -> Context -> Core (List (Name, Int, GlobalDef))
lookupCtxtName = lookupCtxtName' False

||| Look up a (possible hidden) name in the context.
export
lookupHiddenCtxtName : Name -> Context -> Core (List (Name, Int, GlobalDef))
lookupHiddenCtxtName = lookupCtxtName' True

export
hideName : Name -> Context -> Context
hideName n ctxt = { hidden $= insert n () } ctxt

export
unhideName : Name -> Context -> Context
unhideName n ctxt = { hidden $= delete n } ctxt

export
branchCtxt : Context -> Core Context
branchCtxt ctxt = pure ({ branchDepth $= S } ctxt)

export
commitCtxt : Context -> Core Context
commitCtxt ctxt
    = case branchDepth ctxt of
           Z => pure ctxt
           S Z => -- add all the things from 'staging' to the real array
                  do let a = content ctxt
                     arr <- get Arr
                     coreLift $ commitStaged (toList (staging ctxt)) arr
                     pure ({ staging := empty,
                             branchDepth := Z } ctxt)
           S k => pure ({ branchDepth := k } ctxt)
  where
    -- We know the array must be big enough, because it will have been resized
    -- if necessary in the branch to fit the index we've been given here
    commitStaged : List (Int, ContextEntry) -> IOArray ContextEntry -> IO ()
    commitStaged [] arr = pure ()
    commitStaged ((idx, val) :: rest) arr
        = do writeArray arr idx val
             commitStaged rest arr

-- Specific lookup functions
export
lookupExactBy : (GlobalDef -> a) -> Name -> Context ->
              Core (Maybe a)
lookupExactBy fn n gam
  = do Just gdef <- lookupCtxtExact n gam
            | Nothing => pure Nothing
       pure (Just (fn gdef))

export
lookupNameBy : (GlobalDef -> a) -> Name -> Context ->
             Core (List (Name, Int, a))
lookupNameBy fn n gam
  = do gdef <- lookupCtxtName n gam
       pure (map (\ (n, i, gd) => (n, i, fn gd)) gdef)

export
lookupDefExact : Name -> Context -> Core (Maybe Def)
lookupDefExact = lookupExactBy definition

export
lookupDefName : Name -> Context -> Core (List (Name, Int, Def))
lookupDefName = lookupNameBy definition

export
lookupTyExact : Name -> Context -> Core (Maybe (Term [<]))
lookupTyExact = lookupExactBy type

export
lookupTyName : Name -> Context -> Core (List (Name, Int, Term [<]))
lookupTyName = lookupNameBy type

export
lookupDefTyExact : Name -> Context -> Core (Maybe (Def, Term [<]))
lookupDefTyExact = lookupExactBy (\g => (definition g, type g))

export
newDef : FC -> Name -> RigCount -> SnocList Name ->
         Term [<] -> Visibility -> Def -> GlobalDef
newDef fc n rig vars ty vis def
    = MkGlobalDef
        { location = fc
        , fullname = n
        , type = ty
        , eraseArgs = []
        , safeErase = []
        , specArgs = []
        , inferrable = []
        , definition = def
        , evaldef = Nothing
        , multiplicity = rig
        , localVars = vars
        , visibility = vis
        , totality = unchecked
        , flags = []
        , refersToM = Nothing
        , refersToRuntimeM = Nothing
        , invertible = False
        , compexpr = Nothing
        , namedcompexpr = Nothing
        , sizeChange = []
        }

||| Types that are transformed into a faster representation
||| during codegen.
public export
data BuiltinType : Type where
    BuiltinNatural : BuiltinType
    NaturalToInteger : BuiltinType
    IntegerToNatural : BuiltinType

export
Show BuiltinType where
    show BuiltinNatural = "Natural"
    show NaturalToInteger = "NaturalToInteger"
    show IntegerToNatural = "IntegerToNatural"

export
initDefs : Core Defs
initDefs
    = do gam <- initCtxt
         opts <- defaults
         pure $ MkDefs
           { gamma = gam
           , mutData = []
           , uconstraints = []
           , nextUVar = 0
           , currentNS = mainNS
           , nestedNS = []
           , options = opts
           , toSave = empty
           , nextTag = 100
           , typeHints = empty
           , autoHints = empty
           , openHints = empty
           , localHints = empty
           , saveTypeHints = []
           , saveAutoHints = []
           , transforms = empty
           , saveTransforms = []
           , namedirectives = empty
           , ifaceHash = 5381
           , importHashes = []
           , imported = []
           , allImported = []
           , cgdirectives = []
           , toCompileCase = []
           , incData = []
           , allIncData = []
           , toIR = empty
           , userHoles = empty
           , timer = Nothing
           , warnings = []
           , schemeEvalLoaded = False
           , foreignExports = empty
           , holeNames = []
           }

parameters {auto c : Ref Ctxt Defs}

  -- Beware: if your hashable thing contains (potentially resolved) names,
  -- it'll be better to use addHashWithNames to make the hash independent
  -- of the internal numbering of names.
  export
  addHash : Hashable a => a -> CoreE err ()
  addHash x = update Ctxt { ifaceHash $= flip hashWithSalt x }

  export
  initHash : CoreE err ()
  initHash = update Ctxt { ifaceHash := 5381 }

  export
  addUserHole : Bool -> -- defined in another module?
                Name -> -- hole name
                CoreE err ()
  addUserHole ext n = update Ctxt { userHoles $= insert n ext }

  export
  clearUserHole : Name -> CoreE err ()
  clearUserHole n = update Ctxt { userHoles $= delete n }

  export
  getUserHoles : Core (List Name)
  getUserHoles
      = do defs <- get Ctxt
           let hs = sort (keys (userHoles defs))
           filterM (isHole defs) hs
    where
      -- If a hole is declared in one file and defined in another, its
      -- name won't have been cleared unless we've already looked up its
      -- definition (as addDef needs to be called to clear it). So here
      -- check that it's really a hole
      isHole : Defs -> Name -> Core Bool
      isHole defs n
          = do Just def <- lookupCtxtExact n (gamma defs)
                    | Nothing => pure True
               pure $ case definition def of
                    None => True
                    Hole _ _ => True
                    _ => False

  export
  addDef : Name -> GlobalDef -> CoreE err Int
  addDef n def
      = do defs <- get Ctxt
           (idx, gam') <- addCtxt n def (gamma defs)
           put Ctxt ({ gamma := gam' } defs)
           case definition def of
                None => pure ()
                Hole _ _ => pure ()
                _ => clearUserHole (fullname def)
           pure idx

  export
  updateDef : Name -> (Def -> Maybe Def) -> Core ()
  updateDef n fdef
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact n (gamma defs)
               | Nothing => pure ()
           case fdef (definition gdef) of
                Nothing => pure ()
                Just def' => ignore $ addDef n ({ definition := def',
                                                  evaldef := Nothing } gdef)

  export
  updateTy : Int -> Term [<] -> Core ()
  updateTy i ty
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
                | Nothing => pure ()
           ignore $ addDef (Resolved i) ({ type := ty } gdef)

  export
  setCompiled : Name -> CDef -> Core ()
  setCompiled n cexp
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact n (gamma defs)
                | Nothing => pure ()
           ignore $ addDef n ({ compexpr := Just cexp } gdef)

  export
  addContextEntry : Ref STable (IntMap String) =>
                    Name -> Binary Read -> CoreE err Int
  addContextEntry n def
      = do defs <- get Ctxt
           smap <- get STable
           (idx, gam') <- addEntry n (Coded smap def) (gamma defs)
           put Ctxt ({ gamma := gam' } defs)
           pure idx

  export
  addContextAlias : Name -> Name -> Core ()
  addContextAlias alias full
      = do defs <- get Ctxt
           Nothing <- lookupCtxtExact alias (gamma defs)
               | _ => pure () -- Don't add the alias if the name exists already
           gam' <- newAlias alias full (gamma defs)
           put Ctxt ({ gamma := gam' } defs)

  export
  setCtxt : Context -> Core ()
  setCtxt gam = update Ctxt { gamma := gam }

  export
  resolveName : Name -> Core Int
  resolveName (Resolved idx) = pure idx
  resolveName n
    = do defs <- get Ctxt
         (i, gam') <- getPosition n (gamma defs)
         setCtxt gam'
         pure i

  export
  addName : Name -> Core Int
  addName (Resolved idx) = pure idx
  addName n
    = do defs <- get Ctxt
         (i, gam') <- newEntry n (gamma defs)
         setCtxt gam'
         pure i

  -- Call this before trying alternative elaborations, so that updates to the
  -- context are put in the staging area rather than writing over the mutable
  -- array of definitions.
  -- Returns the old context (the one we'll go back to if the branch fails)
  export
  branch : Core Defs
  branch
    = do ctxt <- get Ctxt
         gam' <- branchCtxt (gamma ctxt)
         setCtxt gam'
         pure ctxt

  -- Call this after trying an elaboration to commit any changes to the mutable
  -- array of definitions once we know they're correct. Only actually commits
  -- when we're right back at the top level
  export
  commit : Core ()
  commit
    = do defs <- get Ctxt
         gam' <- commitCtxt (gamma defs)
         setCtxt gam'

  export
  depth : Core Nat
  depth
    = do defs <- get Ctxt
         pure (branchDepth (gamma defs))

  -- Add a string to the string table, for when writing to TTC
  -- It isn't strictly necessary to do this, since 'toBuf' for String will
  -- also do it, but perhaps it will also be useful to preserve sharing of
  -- Strings (FIXME: not that we currently do, but perhaps we should, hence
  -- returning the String, which could in future be a pointer to a shared
  -- String)
  export
  addString : String -> Core String
  addString s
      = do defs <- get Ctxt
           put Ctxt ({ gamma.stringTable $= Binary.Prims.addString s } defs)
           pure s

export
defNameType : Def -> Maybe NameType
defNameType None = Nothing
defNameType (Function {}) = Just Func
defNameType (ExternDef {}) = Just Func
defNameType (ForeignDef {}) = Just Func
defNameType (DCon _ tag ar) = Just (DataCon tag ar)
defNameType (TCon _ ar) = Just (TyCon ar)
defNameType (Hole {}) = Just Func
defNameType (BySearch {}) = Nothing
defNameType (Guess {}) = Nothing
defNameType ImpBind = Just Bound
defNameType (UniverseLevel {}) = Nothing
defNameType Delayed = Nothing

--- HasNames and instances
-- Conversion between full names and resolved names. We can only do this
-- once we have a context to refer to to get the full names, so we'll
-- define the basic implementations for core terms and definitions here.
public export
interface HasNames a where
  full : Context -> a -> Core a
  resolved : Context -> a -> Core a

export
HasNames a => HasNames (List a) where
  full c ns = full_aux c [] ns
    where full_aux : Context -> List a -> List a -> Core (List a)
          full_aux c res [] = pure (reverse res)
          full_aux c res (n :: ns) = full_aux c (!(full c n):: res) ns


  resolved c ns = resolved_aux c [] ns
    where resolved_aux : Context -> List a -> List a -> Core (List a)
          resolved_aux c res [] = pure (reverse res)
          resolved_aux c res (n :: ns) = resolved_aux c (!(resolved c n) :: res) ns

export
HasNames a => HasNames (Maybe a) where
  full gam Nothing = pure Nothing
  full gam (Just x) = pure $ Just !(full gam x)
  resolved gam Nothing = pure Nothing
  resolved gam (Just x) = pure $ Just !(resolved gam x)

export
HasNames Name where
  full gam (Resolved i)
      = do Just gdef <- lookupCtxtExact (Resolved i) gam
                  -- May occasionally happen when working with metadata.
                  -- It's harmless, so just silently return the resolved name.
                | Nothing => pure (Resolved i)
           pure (fullname gdef)
  full gam n = pure n

  resolved gam (Resolved i)
      = pure (Resolved i)
  resolved gam n
      = do let Just i = getNameID n gam
                    | Nothing => pure n
           pure (Resolved i)

HasNames (NameMap a) where
  full gam nmap
      = insertAll empty (toList nmap)
    where
      insertAll : NameMap a -> List (Name, a) -> Core (NameMap a)
      insertAll ms [] = pure ms
      insertAll ms ((k, v) :: ns)
          = insertAll (insert !(full gam k) v ms) ns

  resolved gam nmap
      = insertAll empty (toList nmap)
    where
      insertAll : NameMap a -> List (Name, a) -> Core (NameMap a)
      insertAll ms [] = pure ms
      insertAll ms ((k, v) :: ns)
          = insertAll (insert !(resolved gam k) v ms) ns

export
HasNames UConstraint where
  full gam (ULT fcx x fcy y)
      = do x' <- full gam x; y' <- full gam y
           pure (ULT fcx x' fcy y')
  full gam (ULE fcx x fcy y)
      = do x' <- full gam x; y' <- full gam y
           pure (ULE fcx x' fcy y')

  resolved gam (ULT fcx x fcy y)
      = do x' <- resolved gam x; y' <- resolved gam y
           pure (ULT fcx x' fcy y')
  resolved gam (ULE fcx x fcy y)
      = do x' <- resolved gam x; y' <- resolved gam y
           pure (ULE fcx x' fcy y')

mutual -- Bah, they are all mutual and we can't forward declare implementations yet
  export
  HasNames (CaseScope vars) where
    full gam (RHS x) = pure (RHS !(full gam x))
    full gam (Arg c x sc) = pure (Arg c x !(full gam sc))

    resolved gam (RHS x) = pure (RHS !(resolved gam x))
    resolved gam (Arg c x sc) = pure (Arg c x !(resolved gam sc))

  export
  HasNames (CaseAlt vars) where
    full gam (ConCase fc x tag y)
        = pure (ConCase fc !(full gam x) tag !(full gam y))
    full gam (DelayCase fc ty arg x)
        = pure (DelayCase fc ty arg !(full gam x))
    full gam (ConstCase fc c x)
        = pure (ConstCase fc c !(full gam x))
    full gam (DefaultCase fc x)
        = pure (DefaultCase fc !(full gam x))

    resolved gam (ConCase fc x tag y)
        = pure (ConCase fc !(resolved gam x) tag !(resolved gam y))
    resolved gam (DelayCase fc ty arg x)
        = pure (DelayCase fc ty arg !(resolved gam x))
    resolved gam (ConstCase fc c x)
        = pure (ConstCase fc c !(resolved gam x))
    resolved gam (DefaultCase fc x)
        = pure (DefaultCase fc !(resolved gam x))

  export
  HasNames a => HasNames (RigCount, a) where
    full gam (c, t) = pure $ (c, !(full gam t))
    resolved gam (c, t) = pure $ (c, !(resolved gam t))

  export
  HasNames (Term vars) where
    full gam (Ref fc x (Resolved i))
        = do Just gdef <- lookupCtxtExact (Resolved i) gam
                  | Nothing => pure (Ref fc x (Resolved i))
             pure (Ref fc x (fullname gdef))
    full gam (Meta fc x i xs)
        = do xs <- traverse (full gam) xs
             pure $ case !(lookupCtxtExact (Resolved i) gam) of
               Nothing => Meta fc x i xs
               Just gdef => Meta fc (fullname gdef) i xs
    full gam (Bind fc x b scope)
        = pure (Bind fc x !(traverse (full gam) b) !(full gam scope))
    full gam (App fc fn c arg)
        = pure (App fc !(full gam fn) c !(full gam arg))
    full gam (As fc s p tm)
        = pure (As fc s !(full gam p) !(full gam tm))
    full gam (Case fc c sc scTy alts)
        = pure (Case fc c !(full gam sc) !(full gam scTy) !(full gam alts))
    full gam (TDelayed fc x y)
        = pure (TDelayed fc x !(full gam y))
    full gam (TDelay fc x t y)
        = pure (TDelay fc x !(full gam t) !(full gam y))
    full gam (TForce fc r y)
        = pure (TForce fc r !(full gam y))
    full gam (TType fc (Resolved i))
        = do Just gdef <- lookupCtxtExact (Resolved i) gam
                  | Nothing => pure (TType fc (Resolved i))
             pure (TType fc (fullname gdef))
    full gam def = pure def

    resolved gam (Ref fc x n)
        = do let Just i = getNameID n gam
                  | Nothing => pure (Ref fc x n)
             pure (Ref fc x (Resolved i))
    resolved gam (Meta fc x y xs)
        = do xs' <- traverse (resolved gam) xs
             let Just i = getNameID x gam
                 | Nothing => pure (Meta fc x y xs')
             pure (Meta fc x i xs')
    resolved gam (Bind fc x b scope)
        = pure (Bind fc x !(traverse (resolved gam) b) !(resolved gam scope))
    resolved gam (App fc fn c arg)
        = pure (App fc !(resolved gam fn) c !(resolved gam arg))
    resolved gam (As fc s p tm)
        = pure (As fc s !(resolved gam p) !(resolved gam tm))
    resolved gam (Case fc c sc scTy alts)
        = pure (Case fc c !(resolved gam sc) !(resolved gam scTy) !(resolved gam alts))
    resolved gam (TDelayed fc x y)
        = pure (TDelayed fc x !(resolved gam y))
    resolved gam (TDelay fc x t y)
        = pure (TDelay fc x !(resolved gam t) !(resolved gam y))
    resolved gam (TForce fc r y)
        = pure (TForce fc r !(resolved gam y))
    resolved gam (TType fc n)
        = do let Just i = getNameID n gam
                  | Nothing => pure (TType fc n)
             pure (TType fc (Resolved i))
    resolved gam tm = pure tm

export
HasNames (Env Term vars) where
  full gam [<] = pure [<]
  full gam (bs :< b)
      = pure $ !(full gam bs) :< !(traverse (full gam) b)

  resolved gam [<] = pure [<]
  resolved gam (bs :< b)
      = pure $ !(resolved gam bs) :< !(traverse (resolved gam) b)

export
HasNames TyConInfo where
  full gam x
      = pure $ { mutWith := !(full gam (mutWith x)),
                 datacons := !(full gam (datacons x)) } x
  resolved gam x
      = pure $ { mutWith := !(resolved gam (mutWith x)),
                 datacons := !(resolved gam (datacons x)) } x

export
HasNames Clause where
  full gam (MkClause env lhs rhs)
     = pure $ MkClause !(full gam env) !(full gam lhs) !(full gam rhs)

  resolved gam (MkClause env lhs rhs)
    = [| MkClause (resolved gam env) (resolved gam lhs) (resolved gam rhs) |]

export
HasNames Def where
  full gam (Function x ctm rtm cs)
      = pure $ Function x !(full gam ctm) !(full gam rtm) !(full gam cs)
  full gam (TCon info arity) = pure $ TCon !(full gam info) arity
  full gam (BySearch x max def) = pure $ BySearch x max !(full gam def)
  full gam (Guess guess e cons) = pure $ Guess !(full gam guess) e cons
  full gam x = pure x

  resolved gam (Function x ctm rtm cs)
      = pure $ Function x !(resolved gam ctm) !(resolved gam rtm) !(resolved gam cs)
  resolved gam (TCon info arity) = pure $ TCon !(resolved gam info) arity
  resolved gam (BySearch x max def) = pure $ BySearch x max !(resolved gam def)
  resolved gam (Guess guess e cons) = pure $ Guess !(resolved gam guess) e cons
  resolved gam x = pure x

export
HasNames PartialReason where
  full gam NotStrictlyPositive = pure NotStrictlyPositive
  full gam (BadCall ns) = pure $ BadCall !(traverse (full gam) ns)
  full gam (RecPath ns) = pure $ RecPath !(traverse (full gam) ns)

  resolved gam NotStrictlyPositive = pure NotStrictlyPositive
  resolved gam (BadCall ns) = pure $ BadCall !(traverse (resolved gam) ns)
  resolved gam (RecPath ns) = pure $ RecPath !(traverse (resolved gam) ns)

export
HasNames Terminating where
  full gam (NotTerminating p) = pure $ NotTerminating !(full gam p)
  full gam t = pure t

  resolved gam (NotTerminating p) = pure $ NotTerminating !(resolved gam p)
  resolved gam t = pure t

export
HasNames Covering where
  full gam IsCovering = pure IsCovering
  full gam (MissingCases ts)
      = pure $ MissingCases !(traverse (full gam) ts)
  full gam (NonCoveringCall ns)
      = pure $ NonCoveringCall !(traverse (full gam) ns)

  resolved gam IsCovering = pure IsCovering
  resolved gam (MissingCases ts)
      = pure $ MissingCases !(traverse (resolved gam) ts)
  resolved gam (NonCoveringCall ns)
      = pure $ NonCoveringCall !(traverse (resolved gam) ns)

export
HasNames Totality where
  full gam (MkTotality t c) = pure $ MkTotality !(full gam t) !(full gam c)
  resolved gam (MkTotality t c) = pure $ MkTotality !(resolved gam t) !(resolved gam c)

export
HasNames SCCall where
  full gam sc = pure $ { fnCall := !(full gam (fnCall sc)) } sc
  resolved gam sc = pure $ { fnCall := !(resolved gam (fnCall sc)) } sc

export
HasNames GlobalDef where
  full gam def
      = pure $ { type := !(full gam (type def)),
                 definition := !(full gam (definition def)),
                 totality := !(full gam (totality def)),
                 refersToM := !(full gam (refersToM def)),
                 refersToRuntimeM := !(full gam (refersToRuntimeM def)),
                 sizeChange := !(traverse (full gam) (sizeChange def))
               } def
  resolved gam def
      = pure $ { type := !(resolved gam (type def)),
                 definition := !(resolved gam (definition def)),
                 totality := !(resolved gam (totality def)),
                 refersToM := !(resolved gam (refersToM def)),
                 refersToRuntimeM := !(resolved gam (refersToRuntimeM def)),
                 sizeChange := !(traverse (resolved gam) (sizeChange def))
               } def

export
HasNames Error where
  full gam (UndefinedName fc n) = pure $ UndefinedName fc !(full gam n)
  full gam (NoDeclaration fc n) = pure $ NoDeclaration fc !(full gam n)
  full gam (BadTypeConType fc n) = pure $ BadTypeConType fc !(full gam n)
  full gam (BadDataConType fc n t)
      = pure $ BadDataConType fc !(full gam n) !(full gam t)
  full gam (AmbiguousName fc n) = pure $ AmbiguousName fc !(full gam n)
  full gam (CantConvert fc defs env t1 t2)
      = pure $ CantConvert fc defs env
                           !(full (gamma defs) t1) !(full (gamma defs) t2)
  full gam (PatternVariableUnifies fc fct env n tm)
      = pure $ PatternVariableUnifies fc fct env !(full gam n) !(full gam tm)
  full gam (CyclicMeta fc env n tm)
      = pure $ CyclicMeta fc env
                           !(full gam n) !(full gam tm)
  full gam (AlreadyDefined fc n) = pure $ AlreadyDefined fc !(full gam n)
  full gam (NotFunctionType fc defs env t1)
      = pure $ NotFunctionType fc defs env !(full (gamma defs) t1)
  full gam (LinearUsed fc i n) = pure $ LinearUsed fc i !(full gam n)
  full gam (LinearMisuse fc n c1 c2)
      = pure $ LinearMisuse fc !(full gam n) c1 c2
  full gam err = pure err

  resolved gam (UndefinedName fc n) = pure $ UndefinedName fc !(resolved gam n)
  resolved gam (NoDeclaration fc n) = pure $ NoDeclaration fc !(resolved gam n)
  resolved gam (BadTypeConType fc n) = pure $ BadTypeConType fc !(resolved gam n)
  resolved gam (BadDataConType fc n t)
      = pure $ BadDataConType fc !(resolved gam n) !(resolved gam t)
  resolved gam (AmbiguousName fc n) = pure $ AmbiguousName fc !(resolved gam n)
  resolved gam (CantConvert fc defs env t1 t2)
      = pure $ CantConvert fc defs env
                           !(resolved (gamma defs) t1) !(resolved (gamma defs) t2)
  resolved gam (PatternVariableUnifies fc fct env n tm)
      = pure $ PatternVariableUnifies fc fct env !(resolved gam n) !(resolved gam tm)
  resolved gam (CyclicMeta fc env n tm)
      = pure $ CyclicMeta fc env
                           !(resolved gam n) !(resolved gam tm)
  resolved gam (AlreadyDefined fc n) = pure $ AlreadyDefined fc !(resolved gam n)
  resolved gam (NotFunctionType fc defs env t1)
      = pure $ NotFunctionType fc defs env !(resolved (gamma defs) t1)
  resolved gam (LinearUsed fc i n) = pure $ LinearUsed fc i !(resolved gam n)
  resolved gam (LinearMisuse fc n c1 c2)
      = pure $ LinearMisuse fc !(resolved gam n) c1 c2
  resolved gam err = pure err

export
HasNames Transform where
  full gam (MkTransform n env lhs rhs)
      = pure $ MkTransform !(full gam n) !(full gam env)
                           !(full gam lhs) !(full gam rhs)

  resolved gam (MkTransform n env lhs rhs)
      = pure $ MkTransform !(resolved gam n) !(resolved gam env)
                           !(resolved gam lhs) !(resolved gam rhs)
