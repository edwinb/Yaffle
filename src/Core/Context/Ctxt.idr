module Core.Context.Ctxt

-- This module includes:
-- * The raw context (the array of definitions in the current file)
-- * Looking up values in the context

-- Context entries read from TTC files will be stored as Binary, so when
-- we look them up, we have to decode them

import Core.Binary
import public Core.Context.Def
import Core.Error
import Core.Options
import Core.TT

import Data.IORef
import Data.Maybe

import Libraries.Data.IntMap
import Libraries.Data.IOArray
import Libraries.Data.NameMap
import Libraries.Data.UserNameMap

import Libraries.Utils.Scheme

public export
record CompiledTerm where
  constructor MkCompiledTerm
  evalTC : SchemeObj Write -- for typechecking, so 'export' names blocked
  evalAll : SchemeObj Write -- for evaluation at the REPL, so compile all fully

public export
record GlobalDef where
  constructor MkGlobalDef
  location : FC
  fullname : Name -- original unresolved name
  type : Term []
  definition : Def
  evaldef : Maybe CompiledTerm
  visibility : Visibility
  totality : Totality
  multiplicity : RigCount

export
TTC GlobalDef where
  toBuf d = ?todo1
  fromBuf = ?todo2

-- Label for array references
export
data Arr : Type where

-- A context entry. If it's never been looked up, we haven't decoded the
-- binary blob yet, so decode it first time
public export
data ContextEntry : Type where
     Coded : IntMap String -> Name -> Binary -> ContextEntry
     Decoded : GlobalDef -> ContextEntry

public export
data PossibleName : Type where
     Direct : Name -> Int -> PossibleName -- full name and resolved name id
     Alias : Name -> -- aliased name (from "import as")
             Name -> Int -> -- real full name and resolved name, as above
             PossibleName

-- All the GlobalDefs. We can only have one context, because name references
-- point at locations in here, and if we have more than one the indices won't
-- match up. So, this isn't polymorphic.
public export
record Context where
    constructor MkContext
    firstEntry : Int -- First entry in the current source file
    nextEntry : Int
    stringTable : StringTable -- map from Strings to Ints, for writing TTC more efficiently
                              -- This is kept up to date when writing to the TTC
    -- Map from full name to its position in the context
    resolvedAs : NameMap Int
    -- Map from usernames to all the possible names in all namespaces
    possibles : UserNameMap (List PossibleName)
    -- Reference to the actual content, indexed by Int
    content : Ref Arr (IOArray ContextEntry)
    -- Branching depth, in a backtracking elaborator. 0 is top level; at lower
    -- levels we need to stage updates rather than add directly to the
    -- 'content' store
    branchDepth : Nat
    -- Things which we're going to add, if this branch succeeds
    staging : IntMap ContextEntry

    -- Namespaces which are visible (i.e. have been imported)
    -- This only matters during evaluation and type checking, to control
    -- access in a program - in all other cases, we'll assume everything is
    -- visible
    visibleNS : List Namespace
    inlineOnly : Bool -- only return things with the 'alwaysReduce' flag
    hidden : NameMap () -- Never return these

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

getContent : Context -> Ref Arr (IOArray ContextEntry)
getContent = content

-- Conversion between full names and resolved names. We can only do this
-- once we have a context to refer to to get the full names, so we'll
-- define the basic implementations for core terms and definitions here.
public export
interface HasNames a where
  full : Context -> a -> Core a
  resolved : Context -> a -> Core a

export
HasNames Name where
  full gam (Resolved i)
      = case lookup i (staging gam) of
             Just (Coded _ n _) => pure n
             Just (Decoded def) => pure (fullname def)
             Nothing => pure (Resolved i)
  full gam n = pure n

  resolved gam (Resolved i)
      = pure (Resolved i)
  resolved gam n
      = do let Just i = getNameID n gam
                    | Nothing => pure n
           pure (Resolved i)

export
HasNames GlobalDef where
  full ctxt def = ?todo_hasnames1
  resolved ctxt def = ?todo_hasnames2

decode : Context -> Int -> (update : Bool) -> ContextEntry ->
         Core GlobalDef
decode gam idx update (Coded stbl _ bin)
    = do b <- newRef Bin bin
         st <- newRef STable stbl
         def <- ttc $ fromBuf {a = GlobalDef}

         let a = getContent gam
         arr <- get Arr
         def' <- resolved gam def
         when update $ coreLift $ writeArray arr idx (Decoded def')
         pure def'
decode gam idx update (Decoded def) = pure def

returnDef : Bool -> Int -> GlobalDef -> Maybe (Int, GlobalDef)
returnDef False idx def = Just (idx, def)
returnDef True idx def
    = case definition def of
           Function pi _ =>
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

hideName : Name -> Context -> Context
hideName n ctxt = { hidden $= insert n () } ctxt

unhideName : Name -> Context -> Context
unhideName n ctxt = { hidden $= delete n } ctxt

branchCtxt : Context -> Core Context
branchCtxt ctxt = pure ({ branchDepth $= S } ctxt)

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

export
newDef : FC -> Name -> RigCount -> List Name ->
         Term [] -> Visibility -> Def -> GlobalDef
newDef fc n rig vars ty vis def
    = MkGlobalDef
        { location = fc
        , fullname = n
        , type = ty
        , definition = def
        , evaldef = Nothing
        , visibility = vis
        , totality = unchecked
        , multiplicity = rig
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

public export
record Defs where
  constructor MkDefs
  gamma : Context
  currentNS : Namespace -- namespace for current definitions
  nestedNS : List Namespace -- other nested namespaces we can look in
  options : Options
  toSave : NameMap ()
  nextTag : Int
  typeHints : NameMap (List (Name, Bool))
     -- ^ a mapping from type names to hints (and a flag setting whether it's
     -- a "direct" hint). Direct hints are searched first (as part of a group)
     -- the indirect hints. Indirect hints, in practice, are used to find
     -- instances of parent interfaces, and we don't search these until we've
     -- tried to find a direct result via a constructor or a top level hint.
  autoHints : NameMap Bool
     -- ^ global search hints. A mapping from the hint name, to whether it is
     -- a "default hint". A default hint is used only if all other attempts
     -- to search fail (this flag is really only intended as a mechanism
     -- for defaulting of literals)
  openHints : NameMap ()
     -- ^ currently open global hints; just for the rest of this module (not exported)
     -- and prioritised
  localHints : NameMap ()
     -- ^ Hints defined in the current environment
  saveTypeHints : List (Name, Name, Bool)
     -- We don't look up anything in here, it's merely for saving out to TTC.
     -- We save the hints in the 'GlobalDef' itself for faster lookup.
  saveAutoHints : List (Name, Bool)
  namedirectives : NameMap (List String)
  ifaceHash : Int
  importHashes : List (Namespace, Int)
     -- ^ interface hashes of imported modules
  imported : List (ModuleIdent, Bool, Namespace)
     -- ^ imported modules, whether to rexport, as namespace
  allImported : List (String, (ModuleIdent, Bool, Namespace))
     -- ^ all imported filenames/namespaces, just to avoid loading something
     -- twice unnecessarily (this is a record of all the things we've
     -- called 'readFromTTC' with, in practice)
  userHoles : NameMap Bool
     -- ^ Metavariables the user still has to fill in. In practice, that's
     -- everything with a user accessible name and a definition of Hole.
     -- The Bool says whether it was introduced in another module.

-- Label for context references
export
data Ctxt : Type where

export
initDefs : Core Defs
initDefs
    = do gam <- initCtxt
         opts <- defaults
         pure $ MkDefs
           { gamma = gam
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
           , namedirectives = empty
           , ifaceHash = 5381
           , importHashes = []
           , imported = []
           , allImported = []
           , userHoles = empty
           }
