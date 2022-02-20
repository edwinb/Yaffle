module Core.Context.Def

-- This module includes:
-- * The forms of definition (function, data type etc)
-- * The raw context (the array of definitions in the current file)
-- * Looking up values in the context

-- Context entries read from TTC files will be stored as Binary, so when
-- we look them up, we have to decode them

import Core.Binary
import Core.Error
import Core.TT

import Data.IORef

import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Util
import Libraries.Data.IntMap
import Libraries.Data.IOArray
import Libraries.Data.NameMap
import Libraries.Data.UserNameMap

public export
record FnInfo where
  constructor MkFnInfo
  alwaysReduce : Bool -- Always reduce - typically for inlinable metavar sulutions

public export
record ConInfo where
  constructor MkConInfo
  newTypeArg : Maybe (Bool, Nat)
               -- if it's the only constructor, and only one argument is
               -- non-Rig0, flag it here.
               -- The Nat is the unerased argument position.
               -- The Bool is 'True' if there is no %World token in the
               -- structure, which means it is safe to completely erase
               -- when pattern matching (otherwise we still have to ensure
               -- that the value is inspected, to make sure external effects
               -- happen)

public export
record TyConInfo where
  constructor MkTyConInfo
  paramPos : List Nat -- parameter positions
  deterArgs : List Nat -- determining argument positions (for search)
  mutWith : List Name -- Names this type is defined with mutually
  datacons : List Name -- This type's data constructors
  detagBy : Maybe (List Nat)
                    -- argument positions which can be used for
                    -- detagging, if it's possible (to check if it's
                    -- safe to erase)

public export
data Def : Type where
    None : Def -- Not yet defined
    Function : FnInfo -> Term [] -> Def -- normal function
    DCon : ConInfo ->
           (tag : Int) -> (arity : Nat) -> Def -- data constructor
    TCon : TyConInfo ->
           (tag : Int) -> (arity : Nat) -> Def -- type constructor
    Hole : (numlocs : Nat) -> -- Number of locals in scope at binding point
                              -- (mostly to help display)
           Def
    BySearch : RigCount -> (maxdepth : Nat) -> (defining : Name) -> Def
         -- ^ a name which will be found via auto-search
    -- Constraints are integer references into the current map of
    -- constraints in the UnifyState (see Core.UnifyState)
    Guess : (guess : Term []) ->
            (envbind : Nat) -> -- Number of things in the environment when
                               -- we guessed the term
            (constraints : List Int) -> Def

    ExternDef : (arity : Nat) -> Def -- an external primitive
    ForeignDef : (arity : Nat) ->
                 List String -> -- supported calling conventions,
                                -- e.g "C:printf,libc,stdlib.h", "scheme:display", ...
                 Def
    Builtin : {arity : Nat} -> PrimFn arity -> Def -- primitive
    ImpBind : Def -- global name temporarily standing for an implicitly bound name
    UniverseLevel : Integer -> Def -- a name standing for a universe level in a Type
    -- A delayed elaboration. The elaborators themselves are stored in the
    -- unification state
    Delayed : Def

public export
data Visibility = Private | Export | Public

export
Show Visibility where
  show Private = "private"
  show Export = "export"
  show Public = "public export"

export
Pretty Visibility where
  pretty Private = pretty "private"
  pretty Export = pretty "export"
  pretty Public = pretty "public" <+> pretty "export"

export
Eq Visibility where
  Private == Private = True
  Export == Export = True
  Public == Public = True
  _ == _ = False

export
Ord Visibility where
  compare Private Export = LT
  compare Private Public = LT
  compare Export Public = LT

  compare Private Private = EQ
  compare Export Export = EQ
  compare Public Public = EQ

  compare Export Private = GT
  compare Public Private = GT
  compare Public Export = GT

public export
data TotalReq = Total | CoveringOnly | PartialOK

export
Eq TotalReq where
    (==) Total Total = True
    (==) CoveringOnly CoveringOnly = True
    (==) PartialOK PartialOK = True
    (==) _ _ = False

||| Bigger means more requirements
||| So if a definition was checked at b, it can be accepted at a <= b.
export
Ord TotalReq where
  PartialOK <= _ = True
  _ <= Total = True
  a <= b = a == b

  a < b = a <= b && a /= b

export
Show TotalReq where
    show Total = "total"
    show CoveringOnly = "covering"
    show PartialOK = "partial"

public export
data PartialReason
       = NotStrictlyPositive
       | BadCall (List Name)
       | RecPath (List Name)

export
Show PartialReason where
  show NotStrictlyPositive = "not strictly positive"
  show (BadCall [n])
      = "possibly not terminating due to call to " ++ show n
  show (BadCall ns)
      = "possibly not terminating due to calls to " ++ showSep ", " (map show ns)
  show (RecPath ns)
      = "possibly not terminating due to recursive path " ++ showSep " -> " (map show ns)

export
Pretty PartialReason where
  pretty NotStrictlyPositive = reflow "not strictly positive"
  pretty (BadCall [n])
    = reflow "possibly not terminating due to call to" <++> pretty n
  pretty (BadCall ns)
    = reflow "possibly not terminating due to calls to" <++> concatWith (surround (comma <+> space)) (pretty <$> ns)
  pretty (RecPath ns)
    = reflow "possibly not terminating due to recursive path" <++> concatWith (surround (pretty " -> ")) (pretty <$> ns)

public export
data Terminating
       = Unchecked
       | IsTerminating
       | NotTerminating PartialReason

export
Show Terminating where
  show Unchecked = "not yet checked"
  show IsTerminating = "terminating"
  show (NotTerminating p) = show p

export
Pretty Terminating where
  pretty Unchecked = reflow "not yet checked"
  pretty IsTerminating = pretty "terminating"
  pretty (NotTerminating p) = pretty p

public export
data Covering
       = IsCovering
       | MissingCases (List (Term []))
       | NonCoveringCall (List Name)

export
Show Covering where
  show IsCovering = "covering"
  show (MissingCases c) = "not covering all cases"
  show (NonCoveringCall [f])
     = "not covering due to call to function " ++ show f
  show (NonCoveringCall cs)
     = "not covering due to calls to functions " ++ showSep ", " (map show cs)

export
Pretty Covering where
  pretty IsCovering = pretty "covering"
  pretty (MissingCases c) = reflow "not covering all cases"
  pretty (NonCoveringCall [f])
     = reflow "not covering due to call to function" <++> pretty f
  pretty (NonCoveringCall cs)
     = reflow "not covering due to calls to functions" <++> concatWith (surround (comma <+> space)) (pretty <$> cs)

-- Totality status of a definition. We separate termination checking from
-- coverage checking.
public export
record Totality where
     constructor MkTotality
     isTerminating : Terminating
     isCovering : Covering

export
Show Totality where
  show tot
    = let t = isTerminating tot
          c = isCovering tot in
        showTot t c
    where
      showTot : Terminating -> Covering -> String
      showTot IsTerminating IsCovering = "total"
      showTot IsTerminating c = show c
      showTot t IsCovering = show t
      showTot t c = show c ++ "; " ++ show t

export
Pretty Totality where
  pretty (MkTotality IsTerminating IsCovering) = pretty "total"
  pretty (MkTotality IsTerminating c) = pretty c
  pretty (MkTotality t IsCovering) = pretty t
  pretty (MkTotality t c) = pretty c <+> semi <++> pretty t

export
unchecked : Totality
unchecked = MkTotality Unchecked IsCovering

export
isTotal : Totality
isTotal = MkTotality Unchecked IsCovering

export
notCovering : Totality
notCovering = MkTotality Unchecked (MissingCases [])

public export
record GlobalDef where
  location : FC
  fullname : Name -- original unresolved name
  type : Term []
  definition : Def
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
