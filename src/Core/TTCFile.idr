module Core.TTCFile

import Core.Binary
import Core.CompileExpr
import Core.Context
import Core.Context.Log
import Core.Core
import Core.TTC
import Core.Unify.State

import Libraries.Data.IntMap
import Libraries.Data.IOArray
import Libraries.Data.NameMap
import Libraries.Data.StringMap
import System.File

record TTCFile extra (mode : BinaryMode) where
  constructor MkTTCFile
  importHashes : List (RawNamespace, Int)
  totalReq : TotalReq
  incData : List (CG, String, List String)
  context : List (Name, Binary mode)
  userHoles : List Name
  autoHints : List (Name, Bool)
  typeHints : List (Name, Name, Bool)
  imported : List (ModuleIdent, Bool, Namespace)
  nextVar : Int
  currentNS : Namespace
  nestedNS : List Namespace
  pairnames : Maybe PairNames
  rewritenames : Maybe RewriteNames
  primnames : PrimNames
  namedirectives : List (Name, List String)
  cgdirectives : List (CG, String)
  transforms : List (Name, Transform)
  foreignExports : List (Name, (List (String, String)))
  extraData : Maybe extra

HasNames (Int, FC, Name) where
  full c (i, fc, n) = pure (i, fc, !(full c n))
  resolved c (i, fc, n) = pure (i, fc, !(resolved c n))

HasNames (Name, Bool) where
  full c (n, b) = pure (!(full c n), b)
  resolved c (n, b) = pure (!(resolved c n), b)

HasNames (Name, List a) where
  full c (n, b) = pure (!(full c n), b)
  resolved c (n, b) = pure (!(resolved c n), b)

HasNames (Name, Transform) where
  full c (n, b) = pure (!(full c n), !(full c b))
  resolved c (n, b) = pure (!(resolved c n), !(resolved c b))

HasNames (Name, Name, Bool) where
  full c (n1, n2, b) = pure (!(full c n1), !(full c n2), b)
  resolved c (n1, n2, b) = pure (!(resolved c n1), !(resolved c n2), b)

HasNames e => HasNames (TTCFile e b) where
  full gam (MkTTCFile iHashes totalReq incData
                      context userHoles
                      autoHints typeHints
                      imported nextVar currentNS nestedNS
                      pairnames rewritenames primnames
                      namedirectives cgdirectives trans
                      fexp extra)
      = pure $ MkTTCFile iHashes totalReq incData
                         context userHoles
                         !(traverse (full gam) autoHints)
                         !(traverse (full gam) typeHints)
                         imported nextVar currentNS nestedNS
                         !(fullPair gam pairnames)
                         !(fullRW gam rewritenames)
                         !(fullPrim gam primnames)
                         !(full gam namedirectives)
                         cgdirectives
                         !(full gam trans)
                         !(full gam fexp)
                         !(full gam extra)
    where
      fullPair : Context -> Maybe PairNames -> Core (Maybe PairNames)
      fullPair gam Nothing = pure Nothing
      fullPair gam (Just (MkPairNs t f s))
          = pure $ Just $ MkPairNs !(full gam t) !(full gam f) !(full gam s)

      fullRW : Context -> Maybe RewriteNames -> Core (Maybe RewriteNames)
      fullRW gam Nothing = pure Nothing
      fullRW gam (Just (MkRewriteNs e r))
          = pure $ Just $ MkRewriteNs !(full gam e) !(full gam r)

      fullPrim : Context -> PrimNames -> Core PrimNames
      fullPrim gam (MkPrimNs mi ms mc md)
          = [| MkPrimNs (full gam mi) (full gam ms) (full gam mc) (full gam md) |]


  -- I don't think we ever actually want to call this, because after we read
  -- from the file we're going to add them to learn what the resolved names
  -- are supposed to be! But for completeness, let's do it right.
  resolved gam (MkTTCFile iHashes totalReq incData
                      context userHoles
                      autoHints typeHints
                      imported nextVar currentNS nestedNS
                      pairnames rewritenames primnames
                      namedirectives cgdirectives trans
                      fexp extra)
      = pure $ MkTTCFile iHashes totalReq incData
                         context userHoles
                         !(traverse (resolved gam) autoHints)
                         !(traverse (resolved gam) typeHints)
                         imported nextVar currentNS nestedNS
                         !(resolvedPair gam pairnames)
                         !(resolvedRW gam rewritenames)
                         !(resolvedPrim gam primnames)
                         !(resolved gam namedirectives)
                         cgdirectives
                         !(resolved gam trans)
                         !(resolved gam fexp)
                         !(resolved gam extra)
    where
      resolvedPair : Context -> Maybe PairNames -> Core (Maybe PairNames)
      resolvedPair gam Nothing = pure Nothing
      resolvedPair gam (Just (MkPairNs t f s))
          = pure $ Just $ MkPairNs !(resolved gam t) !(resolved gam f) !(resolved gam s)

      resolvedRW : Context -> Maybe RewriteNames -> Core (Maybe RewriteNames)
      resolvedRW gam Nothing = pure Nothing
      resolvedRW gam (Just (MkRewriteNs e r))
          = pure $ Just $ MkRewriteNs !(resolved gam e) !(resolved gam r)

      resolvedPrim : Context -> PrimNames -> Core PrimNames
      resolvedPrim gam (MkPrimNs mi ms mc md)
          = pure $ MkPrimNs !(resolved gam mi)
                            !(resolved gam ms)
                            !(resolved gam mc)
                            !(resolved gam md)

-- NOTE: TTC files are only compatible if the version number is the same,
-- *and* the 'annot/extra' type are the same, or there are no holes/constraints
writeTTCFile : (HasNames extra, TTC extra) =>
               {auto c : Ref Ctxt Defs} ->
               Ref Bin (Binary Write) -> TTCFile extra Write -> Core ()
writeTTCFile b file_in
      = do file <- toFullNames file_in
           ttc $ do
             toBuf (importHashes file)
             toBuf (totalReq file)
             toBuf (incData file)
             toBuf (imported file)
             toBuf (context file)
             toBuf (userHoles file)
             toBuf (autoHints file)
             toBuf (typeHints file)
             toBuf (nextVar file)
             toBuf (currentNS file)
             toBuf (nestedNS file)
             toBuf (pairnames file)
             toBuf (rewritenames file)
             toBuf (primnames file)
             toBuf (namedirectives file)
             toBuf (cgdirectives file)
             toBuf (transforms file)
             toBuf (foreignExports file)
             toBuf (extraData file)

readTTCFile : TTC extra =>
              {auto c : Ref Ctxt Defs} ->
              Bool -> String -> Maybe (Namespace) ->
              Ref Bin (Binary Read) -> Core (TTCFile extra Read)
readTTCFile readall file as b
      = ttc $ do
           importHashes <- fromBuf
           totalReq <- fromBuf
           incData <- fromBuf
           imp <- fromBuf
           if not readall
              then pure (MkTTCFile importHashes totalReq incData
                                   [] [] [] [] []
                                   0 (mkNamespace "") [] Nothing
                                   Nothing
                                   (MkPrimNs Nothing Nothing Nothing Nothing)
                                   [] [] [] [] Nothing)
              else do
                 defs <- fromBuf
                 uholes <- fromBuf
                 autohs <- fromBuf
                 typehs <- fromBuf
                 nextv <- fromBuf
                 cns <- fromBuf
                 nns <- fromBuf
                 pns <- fromBuf
                 rws <- fromBuf
                 prims <- fromBuf
                 nds <- fromBuf
                 cgds <- fromBuf
                 trans <- fromBuf
                 fexp <- fromBuf
                 ex <- fromBuf
                 pure (MkTTCFile importHashes totalReq incData
                                 (map (replaceNS cns) defs) uholes
                                 autohs typehs imp nextv cns nns
                                 pns rws prims nds cgds trans fexp ex)
  where
    -- We don't store full names in 'defs' - we remove the namespace if it's
    -- the same as the current namespace. So, this puts it back.
    replaceNS : Namespace -> (Name, a) -> (Name, a)
    replaceNS ns n@(NS _ _, d) = n
    replaceNS ns (n, d) = (NS ns n, d)

-- Pull out the list of GlobalDefs that we want to save
getSaveDefs : Ref STable StringTable -> List Name -> List (Name, Binary Write) -> Defs ->
              Core (List (Name, Binary Write))
getSaveDefs st [] acc _ = pure acc
getSaveDefs st (n :: ns) acc defs
    = do Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => getSaveDefs st ns acc defs -- 'n' really should exist though!
         bin <- ttc $ initBinaryS st 16384
         ttc $ toBuf !(full (gamma defs) gdef)
         b <- get Bin
         getSaveDefs st ns ((fullname gdef, b) :: acc) defs

-- Write out the things in the context which have been defined in the
-- current source file
export
writeToTTC : (HasNames extra, TTC extra) =>
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             extra -> (sourceFileName : String) ->
             (ttcFileName : String) -> Core ()
writeToTTC extradata sourceFileName ttcFileName
    = do defs <- get Ctxt
         st <- newRef STable (stringTable (gamma defs))
         bin <- ttc $ initBinary st
         ust <- get UST
         gdefs <- getSaveDefs st (keys (toSave defs)) [] defs
         totalReq <- getDefaultTotalityOption
         writeTTCFile bin
                   (MkTTCFile (map (\ (n, i) => (MkRawNS n, i))
                                   (importHashes defs))
                              totalReq
                              (incData defs)
                              gdefs
                              (keys (userHoles defs))
                              (saveAutoHints defs)
                              (saveTypeHints defs)
                              (imported defs)
                              (nextName ust)
                              (currentNS defs)
                              (nestedNS defs)
                              (pairnames (options defs))
                              (rewritenames (options defs))
                              (primnames (options defs))
                              (NameMap.toList (namedirectives defs))
                              (cgdirectives defs)
                              (saveTransforms defs)
                              (NameMap.toList (foreignExports defs))
                              (Just extradata))
         Right ok <- ttc $ writeToFile "TT2" (ifaceHash defs)
                                    ttcFileName !(get Bin)
               | Left err => throw (InternalError (ttcFileName ++ ": " ++ show err))
         pure ()

addGlobalDef : {auto s : Ref STable (IntMap String)} ->
               {auto c : Ref Ctxt Defs} ->
               (modns : ModuleIdent) -> Namespace ->
               (importAs : Maybe Namespace) ->
               (Name, Binary Read) -> Core ()
addGlobalDef modns filens asm (n, def)
    = do defs <- get Ctxt
         codedentry <- lookupContextEntry n (gamma defs)
         -- Don't update the coded entry because some names might not be
         -- resolved yet
         entry <- maybe (pure Nothing)
                        (\ p => do x <- decode (gamma defs) (fst p) False (snd p)
                                   pure (Just x))
                        codedentry
         unless (completeDef entry) $
           ignore $ addContextEntry n def

         whenJust asm $ \ as => addContextAlias (asName modns as n) n

  where
    -- If the definition already exists, don't overwrite it with an empty
    -- definition or hole. This might happen if a function is declared in one
    -- module and defined in another.
    completeDef : Maybe GlobalDef -> Bool
    completeDef Nothing = False
    completeDef (Just def)
        = case definition def of
               None => False
               Hole _ _ => False
               _ => True

addTypeHint : {auto c : Ref Ctxt Defs} ->
              FC -> (Name, Name, Bool) -> Core ()
addTypeHint fc (tyn, hintn, d)
   = do logC "ttc.read" 10 (pure (show !(getFullName hintn) ++ " for " ++
                            show !(getFullName tyn)))
        addHintFor fc tyn hintn d True

addAutoHint : {auto c : Ref Ctxt Defs} -> (Name, Bool) -> Core ()
addAutoHint (hintn_in, d)
    = do hintn <- toResolvedNames hintn_in
         update Ctxt { autoHints $= insert hintn d }

export
updatePair : {auto c : Ref Ctxt Defs} -> Maybe PairNames -> Core ()
updatePair p = update Ctxt { options->pairnames $= (p <+>) }

export
updateRewrite : {auto c : Ref Ctxt Defs} -> Maybe RewriteNames -> Core ()
updateRewrite r = update Ctxt { options->rewritenames $= (r <+>) }

export
updatePrimNames : PrimNames -> PrimNames -> PrimNames
updatePrimNames p
    = { fromIntegerName $= (p.fromIntegerName <+>),
        fromStringName  $= (p.fromStringName  <+>),
        fromCharName    $= (p.fromCharName    <+>),
        fromDoubleName  $= (p.fromDoubleName  <+>)
      }

export
updatePrims : {auto c : Ref Ctxt Defs} -> PrimNames -> Core ()
updatePrims p = update Ctxt { options->primnames $= updatePrimNames p }

export
updateNameDirectives : {auto c : Ref Ctxt Defs} ->
                       List (Name, List String) -> Core ()
updateNameDirectives [] = pure ()
updateNameDirectives ((t, ns) :: nds)
    = do update Ctxt { namedirectives $= insert t ns }
         updateNameDirectives nds

export
updateCGDirectives : {auto c : Ref Ctxt Defs} ->
                     List (CG, String) -> Core ()
updateCGDirectives cgs = update Ctxt { cgdirectives $= nub . (cgs ++) }

export
updateTransforms : {auto c : Ref Ctxt Defs} ->
                   List (Name, Transform) -> Core ()
updateTransforms [] = pure ()
updateTransforms ((n, t) :: ts)
    = do addT !(toResolvedNames n) !(toResolvedNames t)
         updateTransforms ts
  where
    addT : Name -> Transform -> Core ()
    addT n t
        = do defs <- get Ctxt
             case lookup n (transforms defs) of
                  Nothing =>
                     put Ctxt ({ transforms $= insert n [t] } defs)
                  Just ts =>
                     put Ctxt ({ transforms $= insert n (t :: ts) } defs)

export
updateFExports : {auto c : Ref Ctxt Defs} ->
                 List (Name, (List (String, String))) -> Core ()
updateFExports [] = pure ()
updateFExports ((n, conv) :: ns)
    = do defs <- get Ctxt
         put Ctxt ({ foreignExports $= insert n conv } defs)
         updateFExports ns

getNSas : (String, (ModuleIdent, Bool, Namespace)) ->
          (ModuleIdent, Namespace)
getNSas (a, (b, c, d)) = (b, d)

-- Add definitions from a binary file to the current context
-- Returns the "extra" section of the file (user defined data), the interface
-- hash and the list of additional TTCs that need importing
-- (we need to return these, rather than do it here, because after loading
-- the data that's when we process the extra data...)
export
readFromTTC : TTC extra =>
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              Bool -> -- set nested namespaces (for records, to use at the REPL)
              FC ->
              Bool -> -- importing as public
              (fname : String) -> -- file containing the module
              (modNS : ModuleIdent) -> -- module namespace
              (importAs : Namespace) -> -- namespace to import as
              Core (Maybe (Maybe extra, Int,
                           List (ModuleIdent, Bool, Namespace)))
readFromTTC nestedns loc reexp fname modNS importAs
    = do defs <- get Ctxt
         -- If it's already in the context, with the same visibility flag,
         -- don't load it again (we do need to load it again if it's visible
         -- this time, because we need to reexport the dependencies.)
         let False = (modNS, reexp, importAs) `elem` map snd (allImported defs)
              | True => pure Nothing
         put Ctxt ({ allImported $= ((fname, (modNS, reexp, importAs)) :: ) } defs)

         Right (buffer, ifaceHash) <- ttc $ readFromFile "TT2" fname
               | Left err => throw (InternalError (fname ++ ": " ++ show err))
         bin <- newRef Bin buffer -- for reading the file into
         let as = if importAs == miAsNamespace modNS
                     then Nothing
                     else Just importAs

         -- If it's already imported, but without reexporting, then all we're
         -- interested in is returning which other modules to load.
         -- Otherwise, add the data
         if alreadyDone modNS importAs (allImported defs)
            then do ttc <- readTTCFile False fname as bin
                    let ex = extraData ttc
                    pure (Just (ex, ifaceHash, imported ttc))
            else do
               ttc <- readTTCFile True fname as bin
               let ex = extraData ttc
               let st = table !(get Bin)
               s <- newRef STable st
               traverse_ (addGlobalDef modNS (currentNS ttc) as) (context ttc)
               traverse_ (addUserHole True) (userHoles ttc)
               setNS (currentNS ttc)
               when nestedns $ setNestedNS (nestedNS ttc)
               -- Only do the next batch if the module hasn't been loaded
               -- in any form
               unless (modNS `elem` map (fst . getNSas) (allImported defs)) $
               -- Set up typeHints and autoHints based on the loaded data
                 do traverse_ (addTypeHint loc) (typeHints ttc)
                    traverse_ addAutoHint (autoHints ttc)
                    addImportedInc modNS (incData ttc)
                    -- Set up pair/rewrite etc names
                    updatePair (pairnames ttc)
                    updateRewrite (rewritenames ttc)
                    updatePrims (primnames ttc)
                    updateNameDirectives (reverse (namedirectives ttc))
                    updateCGDirectives (cgdirectives ttc)
                    updateTransforms (transforms ttc)
                    updateFExports (foreignExports ttc)

               when (not reexp) clearSavedHints
               resetFirstEntry

               -- Finally, update the unification state with the holes from the
               -- ttc
               update UST { nextName := nextVar ttc }
               pure (Just (ex, ifaceHash, imported ttc))
  where
    alreadyDone : ModuleIdent -> Namespace ->
                  List (String, (ModuleIdent, Bool, Namespace)) ->
                  Bool
    alreadyDone modns importAs [] = False
      -- If we've already imported 'modns' as 'importAs', or we're importing
      -- 'modns' as itself and it's already imported as anything, then no
      -- need to load again.
    alreadyDone modns importAs ((_, (m, _, a)) :: rest)
        = (modns == m && importAs == a)
          || (modns == m && miAsNamespace modns == importAs)
          || alreadyDone modns importAs rest

-- Process just enough to get the hashes of the imported modules
export
readImportHashes
         : (headerID : String) -> -- TTM or TT2
           (fname : String) ->
           CoreTTC (List (Namespace, Int))
readImportHashes hdr fname
    = do Right buffer <- readNoStringTable hdr fname
             | _ => pure []
         bin <- newRef Bin buffer -- for reading the file into
         importHashes <- fromBuf
         pure (map toNS importHashes)
   where
     toNS : (RawNamespace, Int) -> (Namespace, Int)
     toNS (MkRawNS ns, i) = (ns, i)
