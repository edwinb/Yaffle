module Idris.Error

import Core.Binary
import Core.Core
import Core.Context
import Core.Env
import Core.Evaluate
import Core.Options

import Idris.Doc.String
import Idris.REPL.Opts
import Idris.Resugar
import Idris.Syntax
import Idris.Pretty

import Parser.Source

import Data.List
import Data.List1
import Data.String

import Libraries.Data.List.Extra
import Libraries.Data.List1 as Lib
import Libraries.Data.String.Extra
import Libraries.Text.PrettyPrint.Prettyprinter.Util

import System.File

%default covering

keyword : Doc IdrisAnn -> Doc IdrisAnn
keyword = annotate (Syntax Keyword)

-- | Add binding site information if the term is simply a machine-inserted name
pShowMN : {vars : _} -> Term vars -> Env t vars -> Doc IdrisAnn -> Doc IdrisAnn
pShowMN t env acc = case t of
  Local fc _ p => case dropAllNS (nameAt p) of
      MN _ _ => acc <++> parens ("implicitly bound at" <++> pretty0 (getBinderLoc p env))
      _ => acc
  _ => acc

pshow : {vars : _} ->
        {auto c : Ref Ctxt Defs} ->
        {auto s : Ref Syn SyntaxInfo} ->
        Env Term vars -> Term vars -> Core (Doc IdrisAnn)
pshow env tm
    = do ntm <- normaliseHoles env tm
         itm <- resugar env ntm
         pure (pShowMN ntm env $ prettyBy Syntax itm)

pshowNoNorm : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Env Term vars -> Term vars -> Core (Doc IdrisAnn)
pshowNoNorm env tm
    = do defs <- get Ctxt
         itm <- resugar env tm
         pure (pShowMN tm env $ prettyBy Syntax itm)

ploc : {auto o : Ref ROpts REPLOpts} ->
       FC -> Core (Doc IdrisAnn)
ploc fc = do
    let Just (fn, s, e) = isNonEmptyFC fc
        | Nothing => pure emptyDoc
    let (sr, sc) = mapHom (fromInteger . cast) s
    let (er, ec) = mapHom (fromInteger . cast) e
    let nsize = length $ show (er + 1)
    let head = annotate FileCtxt (pretty0 fc)
    source <- lines <$> getCurrentElabSource
    if sr == er
       then do
         let emph = spaces (cast $ nsize + sc + 4) <+> annotate Error (pretty0 (replicate (ec `minus` sc) '^'))
         let firstr = er `minus` 4
         pure $ vsep ([emptyDoc, head] ++ (addLineNumbers nsize firstr (pretty0 <$> extractRange firstr er source)) ++ [emph]) <+> line
       else pure $ vsep (emptyDoc :: head :: addLineNumbers nsize sr (pretty0 <$> extractRange sr (Prelude.min er (sr + 5)) source)) <+> line
  where
    extractRange : Nat -> Nat -> List String -> List String
    extractRange s e xs = take ((e `minus` s) + 1) (drop s xs)
    pad : Nat -> String -> String
    pad size s = replicate (size `minus` length s) '0' ++ s
    addLineNumbers : Nat -> Nat -> List (Doc IdrisAnn) -> List (Doc IdrisAnn)
    addLineNumbers size st xs =
      snd $ foldl (\(i, s), l => (S i, snoc s (space <+> annotate FileCtxt (pretty0 (pad size $ show $ i + 1) <++> pipe) <++> l))) (st, []) xs

-- Assumes the two FCs are sorted
ploc2 : {auto o : Ref ROpts REPLOpts} ->
        FC -> FC -> Core (Doc IdrisAnn)
ploc2 fc1 fc2 =
    do let Just (fn1, s1, e1) = isNonEmptyFC fc1
           | Nothing => ploc fc2
       let Just (fn2, s2, e2) = isNonEmptyFC fc2
           | Nothing => ploc fc1
       let (sr1, sc1) = mapHom (fromInteger . cast) s1
       let (sr2, sc2) = mapHom (fromInteger . cast) s2
       let (er1, ec1) = mapHom (fromInteger . cast) e1
       let (er2, ec2) = mapHom (fromInteger . cast) e2
       if (er2 > the Nat (er1 + 5))
          then pure $ !(ploc (MkFC fn1 s1 e1)) <+> line <+> !(ploc (MkFC fn2 s2 e2))
          else do let nsize = length $ show (er2 + 1)
                  let head = annotate FileCtxt (pretty0 $ MkFC fn1 s1 e2)
                  let firstRow = annotate FileCtxt (spaces (cast $ nsize + 2) <+> pipe)
                  source <- lines <$> getCurrentElabSource
                  case (sr1 == er1, sr2 == er2, sr1 == sr2) of
                       (True, True, True) => do
                         let line = fileCtxt pipe <++> maybe emptyDoc pretty0 (elemAt source sr1)
                         let emph = fileCtxt pipe <++> spaces (cast sc1) <+> error (pretty0 (replicate (ec1 `minus` sc1) '^'))
                                      <+> spaces (cast $ sc2 `minus` ec1) <+> error (pretty0 (replicate (ec2 `minus` sc2) '^'))
                         pure $ vsep [emptyDoc, head, firstRow, fileCtxt (space <+> byShow (sr1 + 1)) <++> align (vsep [line, emph]), emptyDoc]
                       (True, True, False) => do
                         let line1 = fileCtxt pipe <++> maybe emptyDoc pretty0 (elemAt source sr1)
                         let emph1 = fileCtxt pipe <++> spaces (cast sc1) <+> error (pretty0 (replicate (ec1 `minus` sc1) '^'))
                         let line2 = fileCtxt pipe <++> maybe emptyDoc pretty0 (elemAt source sr2)
                         let emph2 = fileCtxt pipe <++> spaces (cast sc2) <+> error (pretty0 (replicate (ec2 `minus` sc2) '^'))
                         let numbered = if (sr2 `minus` er1) == 1
                                           then []
                                           else addLineNumbers nsize (sr1 + 1) (pretty0 <$> extractRange (sr1 + 1) er1 source)
                         pure $ vsep $ [emptyDoc, head, firstRow, fileCtxt (space <+> byShow (sr1 + 1)) <++> align (vsep [line1, emph1])]
                            ++ numbered
                            ++ [fileCtxt (space <+> byShow (sr2 + 1)) <++> align (vsep [line2, emph2]), emptyDoc]
                       (True, False, _) => do
                         let line = fileCtxt pipe <++> maybe emptyDoc pretty0 (elemAt source sr1)
                         let emph = fileCtxt pipe <++> spaces (cast sc1) <+> error (pretty0 (replicate (ec1 `minus` sc1) '^'))
                         pure $ vsep $ [emptyDoc, head, firstRow, fileCtxt (space <+> byShow (sr1 + 1)) <++> align (vsep [line, emph])]
                            ++ addLineNumbers nsize (sr1 + 1) (pretty0 <$> extractRange (sr1 + 1) (Prelude.max er1 er2) source)
                            ++ [emptyDoc]
                       (False, True, True) => do
                         let line = fileCtxt pipe <++> maybe emptyDoc pretty0 (elemAt source sr1)
                         let emph = fileCtxt pipe <++> spaces (cast sc1) <+> error (pretty0 (replicate (ec1 `minus` sc1) '^'))
                         pure $ vsep $ [emptyDoc, head, firstRow, fileCtxt (space <+> byShow (sr1 + 1)) <++> align (vsep [line, emph])]
                            ++ addLineNumbers nsize (sr1 + 1) (pretty0 <$> extractRange (sr1 + 1) (Prelude.max er1 er2) source)
                            ++ [emptyDoc]
                       (False, True, False) => do
                         let top = addLineNumbers nsize (sr1 + 1) (pretty0 <$> extractRange (sr1 + 1) er1 source)
                         let line = fileCtxt pipe <++> maybe emptyDoc pretty0 (elemAt source sr1)
                         let emph = fileCtxt pipe <++> spaces (cast sc2) <+> error (pretty0 (replicate (ec2 `minus` sc2) '^'))
                         pure $ vsep $ [emptyDoc, head, firstRow] ++ top ++ [fileCtxt (space <+> byShow (sr2 + 1)) <++> align (vsep [line, emph]), emptyDoc]
                       (_, _, _) => pure $ vsep (emptyDoc :: head :: addLineNumbers nsize sr1 (pretty0 <$> extractRange sr1 er2 source)) <+> line
  where
    extractRange : Nat -> Nat -> List String -> List String
    extractRange s e xs = take ((e `minus` s) + 1) (drop s xs)
    pad : Nat -> String -> String
    pad size s = replicate (size `minus` length s) '0' ++ s
    addLineNumbers : Nat -> Nat -> List (Doc IdrisAnn) -> List (Doc IdrisAnn)
    addLineNumbers size st xs =
      snd $ foldl (\(i, s), l => (S i, snoc s (space <+> annotate FileCtxt (pretty0 (pad size $ show $ i + 1) <++> pipe) <++> l))) (st, []) xs

export
pwarningRaw : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto o : Ref ROpts REPLOpts} ->
              Warning -> Core (Doc IdrisAnn)
pwarningRaw (ParserWarning fc msg)
    = pure $ pretty0 msg <+> line <+> !(ploc fc)
pwarningRaw (UnreachableClause fc env tm)
    = pure $ errorDesc (reflow "Unreachable clause:"
        <++> code !(pshow env tm))
        <+> line <+> !(ploc fc)
pwarningRaw (ShadowingGlobalDefs fc ns)
    = pure $ vcat
    $ reflow "We are about to implicitly bind the following lowercase names."
   :: reflow "You may be unintentionally shadowing the associated global definitions:"
   :: map pshadowing (forget ns)
   `snoc` !(ploc fc)
  where
    pshadowing : (String, List1 Name) -> Doc IdrisAnn
    pshadowing (n, ns) = indent 2 $ hsep $
                           pretty0 n
                        :: reflow "is shadowing"
                        :: punctuate comma (map pretty0 (forget ns))

pwarningRaw (ShadowingLocalBindings fc ns)
    = pure $ vcat
    [ reflow "You may be unintentionally shadowing the following local bindings:"
    , indent 2 $ hcat $ pretty0 . fst <$> (forget ns)
    , !(ploc fc)
    ]

pwarningRaw (Deprecated s fcAndName)
    = do docs <- traverseOpt (\(fc, name) => getDocsForName fc name justUserDoc) fcAndName
         pure . vsep $ catMaybes [ Just $ "Deprecation warning:" <++> pretty0 s
                                 , reAnnotate (const Pretty.UserDocString) <$> docs
                                 ]
pwarningRaw (GenericWarn s)
    = pure $ pretty0 s

export
pwarning : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto o : Ref ROpts REPLOpts} ->
           Warning -> Core (Doc IdrisAnn)
pwarning wrn = pwarningRaw !(toFullNames wrn)

perrorRaw : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto o : Ref ROpts REPLOpts} ->
            Error -> Core (Doc IdrisAnn)
perrorRaw (Fatal err) = perrorRaw err
perrorRaw (CantConvert fc gam env l r)
    = do defs <- get Ctxt
         put Ctxt gam
         let res = errorDesc (hsep [ reflow "Mismatch between" <+> colon
                  , code !(pshow env l)
                  , "and"
                  , code !(pshow env r) <+> dot
                  ]) <+> line <+> !(ploc fc)
         put Ctxt defs
         pure res
perrorRaw (CantSolveEq fc gam env l r)
    = do defs <- get Ctxt
         put Ctxt gam
         let res = errorDesc (hsep [ reflow "Can't solve constraint between" <+> colon
                      , code !(pshow env l)
                      , "and"
                      , code !(pshow env r) <+> dot
                      ]) <+> line <+> !(ploc fc)
         put Ctxt defs
         pure res
perrorRaw (PatternVariableUnifies fc fct env n tm)
    = do let (min, max) = order fc fct
         pure $ errorDesc (hsep [ reflow "Pattern variable"
                  , code (prettyVar n)
                  , reflow "unifies with" <+> colon
                  , code !(pshow env tm) <+> dot
                  ]) <+> line <+> !(ploc2 min max) <+> line
                     <+> reflow "Suggestion: Use the same name for both pattern variables, since they unify."
  where
    prettyVar : Name -> Doc IdrisAnn
    prettyVar (PV n _) = prettyVar n
    prettyVar n = pretty0 n
    order : FC -> FC -> (FC, FC)
    order fc1 fc2 =
      let Just (_, sr1, sc1) = isNonEmptyFC fc1
           | Nothing => (EmptyFC, fc2)
          Just (_, sr2, sc2) = isNonEmptyFC fc2
           | Nothing => (fc1, EmptyFC)
      in if sr1 < sr2 then (fc1, fc2) else if sr1 == sr2 && sc1 < sc2 then (fc1, fc2) else (fc2, fc1)
perrorRaw (CyclicMeta fc env n tm)
    = pure $ errorDesc (reflow "Cycle detected in solution of metavariable"
        <++> meta (pretty0 !(prettyName n)) <++> equals
        <++> code !(pshow env tm)) <+> line <+> !(ploc fc)
perrorRaw (WhenUnifying _ gam env x y err)
    = do defs <- get Ctxt
         put Ctxt gam
         let res = errorDesc (reflow "When unifying:" <+> line
                   <+> "    " <+> code !(pshow env x) <+> line <+> "and:" <+> line
                   <+> "    " <+> code !(pshow env y)) <+> line <+> !(perrorRaw err)
         put Ctxt defs
         pure res
perrorRaw (ValidCase fc env (Left tm))
    = pure $ errorDesc (code !(pshow env tm) <++> reflow "is not a valid impossible case.")
        <+> line <+> !(ploc fc)
perrorRaw (ValidCase _ env (Right err))
    = pure $ errorDesc (reflow "Impossible pattern gives an error" <+> colon) <+> line <+> !(perrorRaw err)
perrorRaw (UndefinedName fc x)
    = pure $ errorDesc (reflow "Undefined name" <++> code (pretty0 x) <+> dot) <++> line <+> !(ploc fc)
perrorRaw (InvisibleName fc n (Just ns))
    = pure $ errorDesc ("Name" <++> code (pretty0 n) <++> reflow "is inaccessible since"
        <++> code (pretty0 ns) <++> reflow "is not explicitly imported.")
        <+> line <+> !(ploc fc)
        <+> line <+> reflow "Suggestion: add an explicit" <++> keyword "export" <++> "or" <++> keyword ("public" <++> "export")
        <++> reflow "modifier. By default, all names are" <++> keyword "private" <++> reflow "in namespace blocks."
perrorRaw (InvisibleName fc x Nothing)
    = pure $ errorDesc ("Name" <++> code (pretty0 x) <++> reflow "is private.") <+> line <+> !(ploc fc)
        <+> line <+> reflow "Suggestion: add an explicit" <++> keyword "export" <++> "or" <++> keyword ("public" <++> "export")
        <++> reflow "modifier. By default, all names are" <++> keyword "private" <++> reflow "in namespace blocks."
perrorRaw (BadTypeConType fc n)
    = pure $ errorDesc (reflow "Return type of" <++> code (pretty0 n) <++> reflow "must be" <++> code "Type"
        <+> dot) <+> line <+> !(ploc fc)
perrorRaw (BadDataConType fc n fam)
    = pure $ errorDesc (reflow "Return type of" <++> code (pretty0 n) <++> reflow "must be in"
        <++> code (pretty0 fam)) <++> line <+> !(ploc fc)
perrorRaw (NotCovering fc n IsCovering)
    = pure $ errorDesc (reflow "Internal error" <++> parens (reflow "Coverage of" <++> code (pretty0 n)))
perrorRaw (NotCovering fc n (MissingCases cs))
    = pure $ errorDesc (code (pretty0 !(prettyName n)) <++> reflow "is not covering.")
        <+> line <+> !(ploc fc) <+> line
        <+> reflow "Missing cases" <+> colon <+> line
        <+> indent 4 (vsep !(traverse (pshow [<]) cs)) <+> line
perrorRaw (NotCovering fc n (NonCoveringCall ns))
    = pure $ errorDesc (pretty0 !(prettyName n) <++> reflow "is not covering.")
        <+> line <+> !(ploc fc) <+> line
        <+> reflow "Calls non covering function" <+>
        case ns of
             [fn] => space <+> pretty0 fn
             _ => pretty0 's' <+> colon <++> concatWith (surround (comma <+> space)) (pretty0 <$> ns)
perrorRaw (NotTotal fc n r)
    = pure $ errorDesc (code (pretty0 !(prettyName n)) <++> reflow "is not total," <++> pretty0 r)
        <+> line <+> !(ploc fc)
perrorRaw (LinearUsed fc count n)
    = pure $ errorDesc (reflow "There are" <++> byShow count <++> reflow "uses of linear name"
        <++> code (pretty0 (sugarName n)) <+> dot)
        <++> line <+> !(ploc fc)
        <+> line <+> reflow "Suggestion: linearly bounded variables must be used exactly once."
perrorRaw (LinearMisuse fc n exp ctx)
    = if isErased exp
         then pure $ errorDesc (code (pretty0 n) <++> reflow "is not accessible in this context.")
                <+> line <+> !(ploc fc)
         else pure $ errorDesc (reflow "Trying to use" <++> prettyRig exp <++> "name"
                <++> code (pretty0 (sugarName n)) <++> "in" <++> prettyRel ctx <++> "context.")
                <+> line <+> !(ploc fc)
  where
    prettyRig : RigCount -> Doc ann
    prettyRig = elimSemi "irrelevant"
                         "linear"
                         (const "unrestricted")

    prettyRel : RigCount -> Doc ann
    prettyRel = elimSemi "irrelevant"
                         "relevant"
                         (const "non-linear")
perrorRaw (InconsistentUse fc ns)
    = pure $ errorDesc (hsep
                (reflow "Inconsistent usage of names in case branches:"
                   :: !(traverse branch ns)))
  where
    branch : (FC, List Name) -> Core (Doc IdrisAnn)
    branch (fc, [])
        = pure $ reflow "No linear usage in " <++> !(ploc fc)
    branch (fc, ns)
        = pure $ concatWith (surround ",") (map pretty0 ns) <++>
                 reflow "used in" <++> !(ploc fc)
perrorRaw (BorrowPartial fc env tm arg)
    = pure $ errorDesc (code !(pshow env tm) <++> reflow "borrows argument" <++> code !(pshow env arg)
        <++> reflow "so must be fully applied.")
        <+> line <+> !(ploc fc)
perrorRaw (BorrowPartialType fc env tm)
    = pure $ errorDesc (code !(pshow env tm) <++>
        reflow "borrows, so must return a concrete type.") <+> line <+> !(ploc fc)
perrorRaw (AmbiguousName fc ns)
    = pure $ errorDesc (reflow "Ambiguous name" <++> code (cast $ prettyList ns))
        <+> line <+> !(ploc fc)
perrorRaw (AmbiguousElab fc env ts_in)
    = do pp <- getPPrint
         setPPrint ({ fullNamespace := True } pp)
         ts_show <- traverse (\ (gam, t) =>
                                  do defs <- get Ctxt
                                     put Ctxt gam
                                     res <- pshow env t
                                     put Ctxt defs
                                     pure res) ts_in
         let res = vsep [ errorDesc (reflow "Ambiguous elaboration. Possible results" <+> colon)
                        , indent 4 (vsep ts_show)
                        ] <+> line <+> !(ploc fc)
         setPPrint pp
         pure res
perrorRaw (AmbiguousSearch fc env tgt ts)
    = pure $ vsep [ errorDesc (reflow "Multiple solutions found in search of" <+> colon)
                  , indent 4 !(pshowNoNorm env tgt)
                  , !(ploc fc)
                  , reflow "Possible correct results" <+> colon
                  , indent 4 (vsep !(traverse (pshowNoNorm env) ts))
                  ]
perrorRaw (AmbiguityTooDeep fc n ns)
    = pure $ errorDesc (reflow "Maximum ambiguity depth exceeded in" <++> code (pretty0 !(getFullName n))
        <+> colon) <+> line <+> concatWith (surround " --> ") (pretty0 <$> !(traverse getFullName ns))
        <++> line <+> !(ploc fc)
        <+> line <+> reflow "Suggestion: the default ambiguity depth limit is 3, the" <++> code "%ambiguity_depth"
        <++> reflow "pragma can be used to extend this limit, but beware compilation times can be severely impacted."
perrorRaw (AllFailed ts)
    = case allUndefined ts of
           Just e => perrorRaw e
           _ => pure $ errorDesc (reflow "Sorry, I can't find any elaboration which works. All errors" <+> colon) <+> line
                  <+> vsep !(traverse pAlterror ts)
  where
    pAlterror : (Maybe Name, Error) -> Core (Doc IdrisAnn)
    pAlterror (Just n, err)
       = pure $ "If" <++> code (pretty0 !(aliasName !(getFullName n))) <+> colon <++> !(perrorRaw err)
    pAlterror (Nothing, err)
       = pure $ reflow "Possible error" <+> colon <+> line <+> indent 4 !(perrorRaw err)

    allUndefined : List (Maybe Name, Error) -> Maybe Error
    allUndefined [] = Nothing
    allUndefined [(_, err@(UndefinedName _ _))] = Just err
    allUndefined ((_, err@(UndefinedName _ _)) :: es) = allUndefined es
    allUndefined _ = Nothing
perrorRaw (RecordTypeNeeded fc _)
    = pure $ errorDesc (reflow "Can't infer type for this record update.") <+> line <+> !(ploc fc)
perrorRaw (DuplicatedRecordUpdatePath fc ps)
    = pure $ vcat $
      errorDesc (reflow "Duplicated record update paths:")
      :: map (indent 2 . reAnnotate Syntax . prettyFieldPath) ps
      ++ [line <+> !(ploc fc)]
perrorRaw (NotRecordField fc fld Nothing)
    = pure $ errorDesc (code (pretty0 fld) <++> reflow "is not part of a record type.") <+> line <+> !(ploc fc)
perrorRaw (NotRecordField fc fld (Just ty))
    = pure $ errorDesc (reflow "Record type" <++> code (pretty0 !(getFullName ty)) <++> reflow "has no field"
        <++> code (pretty0 fld) <+> dot) <+> line <+> !(ploc fc)
perrorRaw (NotRecordType fc ty)
    = pure $ errorDesc (code (pretty0 !(getFullName ty)) <++> reflow "is not a record type.") <+> line <+> !(ploc fc)
perrorRaw (IncompatibleFieldUpdate fc flds)
    = pure $ reflow "Field update" <++> reAnnotate Syntax (prettyFieldPath flds)
             <++> reflow "not compatible with other updates at" <+> colon <+> line <+> !(ploc fc)
perrorRaw (InvalidArgs fc env [n] tm)
    = pure $ errorDesc (code (pretty0 n) <++> reflow "is not a valid argument in" <++> !(pshow env tm)
        <+> dot) <+> line <+> !(ploc fc)
perrorRaw (InvalidArgs fc env ns tm)
    = pure $ errorDesc (concatWith (surround (comma <+> space)) (code . pretty0 <$> ns)
        <++> reflow "are not valid arguments in" <++> !(pshow env tm) <+> dot)
        <+> line <+> !(ploc fc)
perrorRaw (TryWithImplicits fc env imps)
    = pure $ errorDesc (reflow "Need to bind implicits"
        <++> concatWith (surround (comma <+> space)) !(traverse (tshow env) imps) <+> dot)
        <+> line <+> !(ploc fc)
  where
    tshow : {vars : _} ->
            Env Term vars -> (Name, Term vars) -> Core (Doc IdrisAnn)
    tshow env (n, ty) = pure $ pretty0 n <++> colon <++> code !(pshow env ty)
perrorRaw (BadUnboundImplicit fc env n ty)
    = pure $ errorDesc (reflow "Can't bind name" <++> code (pretty0 (nameRoot n))
        <++> reflow "with type" <++> code !(pshow env ty)
        <+> colon) <+> line <+> !(ploc fc) <+> line <+> reflow "Suggestion: try an explicit bind."
perrorRaw (CantSolveGoal fc gam env g reason)
    = do defs <- get Ctxt
         put Ctxt gam
         let (_ ** (env', g')) = dropEnv env g
         let res = errorDesc (reflow "Can't find an implementation for" <++> code !(pshow env' g')
                     <+> dot) <+> line <+> !(ploc fc)
         put Ctxt defs
         case reason of
              Nothing => pure res
              Just r => do rdesc <- perrorRaw r
                           pure (res <+> line <+>
                                 (reflow "Possible cause:" <++> rdesc))
  where
    -- For display, we don't want to see the full top level type; just the
    -- return type
    dropEnv : {vars : _} ->
              Env Term vars -> Term vars ->
              (ns ** (Env Term ns, Term ns))
    dropEnv env (Bind _ n b@(Pi _ _ _ _) sc) = dropEnv (env :< b) sc
    dropEnv env (Bind _ n b@(Let _ _ _ _) sc) = dropEnv (env :< b) sc
    dropEnv env tm = (_ ** (env, tm))

perrorRaw (DeterminingArg fc n i env g)
    = pure $ errorDesc (reflow "Can't find an implementation for" <++> code !(pshow env g) <+> line
        <+> reflow "since I can't infer a value for argument" <++> code (pretty0 n) <+> dot)
        <+> line <+> !(ploc fc)
perrorRaw (UnsolvedHoles hs)
    = pure $ errorDesc (reflow "Unsolved holes" <+> colon) <+> line <+> !(prettyHoles hs)
  where
    prettyHoles : List (FC, Name) -> Core (Doc IdrisAnn)
    prettyHoles [] = pure emptyDoc
    prettyHoles ((fc, n) :: hs)
        = pure $ meta (pretty0 n) <++> reflow "introduced at:" <++> !(ploc fc) <+> !(prettyHoles hs)
perrorRaw (CantInferArgType fc env n h ty)
    = pure $ errorDesc (reflow "Can't infer type for argument" <++> code (pretty0 n)) <+> line
        <+> "Got" <++> code !(pshow env ty) <++> reflow "with hole" <++> meta (pretty0 h) <+> dot
        <+> line <+> !(ploc fc)
perrorRaw (SolvedNamedHole fc env h tm)
    = pure $ errorDesc (reflow "Named hole" <++> meta (pretty0 h)
        <++> reflow "has been solved by unification.") <+> line
        <+> "Result" <+> colon <++> code !(pshow env tm)
        <+> line <+> !(ploc fc)
perrorRaw (VisibilityError fc vx x vy y)
    = pure $ errorDesc (keyword (pretty0 vx) <++> code (pretty0 (sugarName x))
        <++> reflow "cannot refer to" <++> keyword (pretty0 vy) <++> code (pretty0 (sugarName y)))
        <+> line <+> !(ploc fc)
perrorRaw (NonLinearPattern fc n)
    = pure $ errorDesc (reflow "Non linear pattern" <++> code (pretty0 (sugarName n)) <+> dot)
        <+> line <+> !(ploc fc)
perrorRaw (BadPattern fc n)
    = pure $ errorDesc (reflow "Pattern not allowed here" <+> colon <++> code (pretty0 n) <+> dot)
        <+> line <+> !(ploc fc)
perrorRaw (NoDeclaration fc n)
    = pure $ errorDesc (reflow "No type declaration for" <++> code (pretty0 n) <+> dot)
        <+> line <+> !(ploc fc)
perrorRaw (AlreadyDefined fc n)
    = pure $ errorDesc (code (pretty0 n) <++> reflow "is already defined.")
        <+> line <+> !(ploc fc)
perrorRaw (NotFunctionType fc gam env tm)
    = do defs <- get Ctxt
         put Ctxt gam
         let res = errorDesc (code !(pshow env tm) <++> reflow "is not a function type.")
                    <+> line <+> !(ploc fc)
         put Ctxt defs
         pure res
perrorRaw (RewriteNoChange fc gam env rule ty)
    = do defs <- get Ctxt
         put Ctxt gam
         let res = errorDesc (reflow "Rewriting by"
                      <++> code !(pshow env rule)
                      <++> reflow "did not change type"
                      <++> code !(pshow env ty) <+> dot)
                      <+> line <+> !(ploc fc)
         put Ctxt defs
         pure res
perrorRaw (NotRewriteRule fc env rule)
    = pure $ errorDesc (code !(pshow env rule) <++> reflow "is not a rewrite rule type.")
        <+> line <+> !(ploc fc)
perrorRaw (CaseCompile fc n DifferingArgNumbers)
    = pure $ errorDesc (reflow "Patterns for" <++> code (pretty0 !(prettyName n))
       <++> reflow "have differing numbers of arguments.")
        <+> line <+> !(ploc fc)
perrorRaw (CaseCompile fc n DifferingTypes)
    = pure $ errorDesc (reflow "Patterns for" <++> code (pretty0 !(prettyName n))
       <++> reflow "require matching on different types.")
        <+> line <+> !(ploc fc)
perrorRaw (CaseCompile fc n UnknownType)
    = pure $ errorDesc (reflow "Can't infer type to match in"
       <++> code (pretty0 !(prettyName n)) <+> dot)
        <+> line <+> !(ploc fc)
perrorRaw (CaseCompile fc n CantResolveType)
    = pure $ errorDesc (reflow "Can't infer argument type in"
       <++> code (pretty0 !(prettyName n)) <+> dot)
        <+> line <+> !(ploc fc)
perrorRaw (CaseCompile fc n (NotFullyApplied cn))
    = pure $ errorDesc ("Constructor" <++> code (pretty0 cn) <++> reflow "is not fully applied.")
         <+> line <+> !(ploc fc)
perrorRaw (CaseCompile fc n (MatchErased (_ ** (env, tm))))
    = pure $ errorDesc (reflow "Attempt to match on erased argument" <++> code !(pshow env tm) <++> "in"
        <++> code (pretty0 !(prettyName n)) <+> dot) <+> line <+> !(ploc fc)
perrorRaw (BadDotPattern fc env reason x y)
    = pure $ errorDesc (reflow "Can't match on" <++> code !(pshow env x)
        <++> parens (pretty reason) <+> dot) <+> line <+> !(ploc fc)
perrorRaw (MatchTooSpecific fc env tm)
    = pure $ errorDesc (reflow "Can't match on" <++> code !(pshow env tm)
        <++> reflow "as it must have a polymorphic type.") <+> line <+> !(ploc fc)
perrorRaw (BadImplicit fc str)
    = pure $ errorDesc (reflow "Can't infer type for unbound implicit name" <++> code (pretty0 str) <+> dot)
        <+> line <+> !(ploc fc) <+> line <+> reflow "Suggestion: try making it a bound implicit."
perrorRaw (BadRunElab fc env script desc)
    = pure $ errorDesc (reflow "Bad elaborator script" <++> code !(pshow env script)
       <++> parens (pretty0 desc) <+> dot)
        <+> line <+> !(ploc fc)
perrorRaw (RunElabFail e)
    = pure $ reflow "Error during reflection" <+> colon <++> !(perrorRaw e)
perrorRaw (GenericMsg fc str) = pure $ pretty0 str <+> line <+> !(ploc fc)
perrorRaw (TTCErr msg)
    = pure $ errorDesc (reflow "Error in TTC file" <+> colon <++> byShow msg)
        <++> parens "the most likely case is that the ./build directory in your current project contains files from a previous build of idris2 or the idris2 executable is from a different build than the installed .ttc files"
perrorRaw (FileErr (SystemFileErr fname err))
    = pure $ errorDesc (reflow "File error in" <++> pretty0 fname <++> colon)
       <++> byShow err
perrorRaw (FileErr (TTFileErr err))
    = pure $ errorDesc (reflow "File error: " <++> reflow err)
perrorRaw (CantFindPackage fname)
    = pure $ errorDesc (reflow "Can't find package " <++> pretty0 fname)
perrorRaw (LitFail fc)
    = pure $ errorDesc (reflow "Can't parse literate.")
        <+> line <+> !(ploc fc)
perrorRaw (LexFail fc msg)
    = pure $ errorDesc (pretty0 msg) <+> line <+> !(ploc fc)
perrorRaw (ParseFail ((fc, msg) ::: Nil))
    = pure $ errorDesc (pretty0 msg) <+> line <+> !(ploc fc)
perrorRaw (ParseFail errs)
    = pure $ errorDesc (reflow "Couldn't parse any alternatives" <+> colon) <+> line <+> !listErrors
  where
    prettyErrors : Nat -> Nat -> List (FC, String) -> Core (Doc IdrisAnn)
    prettyErrors showCount _ []   = pure emptyDoc
    prettyErrors showCount 0 errs = pure $ meta (pretty0 "... (\{show $ length errs} others)")
    prettyErrors showCount (S k) ((fc, msg) :: hs)
        = do let idx = show $ showCount `minus` k
             pure $ warning (pretty0 "\{idx}: \{msg}")
               <+> line <+> !(ploc fc)
               <+> !(prettyErrors showCount k hs)

    listErrors : Core (Doc IdrisAnn)
    listErrors = do showCount <- logErrorCount . session . options <$> get Ctxt
                    prettyErrors showCount showCount . nub . reverse $ forget errs
perrorRaw (ModuleNotFound fc ns)
    = pure $ errorDesc ("Module" <++> annotate FileCtxt (pretty0 ns) <++> reflow "not found")
        <+> line <+> !(ploc fc)
perrorRaw (CyclicImports ns)
    = pure $ errorDesc (reflow "Module imports form a cycle" <+> colon)
        <++> concatWith (surround " -> ") (pretty0 <$> ns)
perrorRaw ForceNeeded = pure $ errorDesc (reflow "Internal error when resolving implicit laziness")
perrorRaw (InternalError str) = pure $ errorDesc (reflow "INTERNAL ERROR" <+> colon) <++> pretty0 str
perrorRaw (UserError str) = pure $ errorDesc ("Error" <+> colon) <++> pretty0 str
perrorRaw (NoForeignCC fc specs) = do
    let cgs = fst <$> availableCGs (options !(get Ctxt))
    let res = vsep [ errorDesc (reflow ("The given specifier '" ++ show specs ++ "' was not accepted by any backend. Available backends") <+> colon)
                   , indent 2 (concatWith (\ x, y => x <+> ", " <+> y) (map reflow cgs))
                   , reflow "Some backends have additional specifier rules, refer to their documentation."
                   ] <+> line <+> !(ploc fc)
    pure res
perrorRaw (BadMultiline fc str)
  = pure $ errorDesc (reflow "While processing multi-line string" <+> dot <++> pretty0 str <+> dot)
      <+> line <+> !(ploc fc)
perrorRaw (Timeout str) = pure $ errorDesc (reflow "Timeout in" <++> pretty0 str)

perrorRaw (FailingDidNotFail fc)
  = pure $ errorDesc (reflow "Failing block did not fail" <+> dot)
    <+> line <+> !(ploc fc)
perrorRaw (FailingWrongError fc msg err)
  = pure $ vcat [ errorDesc (reflow "Failing block failed with the wrong error" <+> dot)
                , "Expected" <++> dquote <+> pretty0 msg <+> dquote <++> "but got:"
                , vsep !(traverse perrorRaw (forget err))
                ]

perrorRaw (InType fc n err)
    = pure $ hsep [ errorDesc (reflow "While processing type of" <++> code (pretty0 !(prettyName n))) <+> dot
                  , !(perrorRaw err)
                  ]
perrorRaw (InCon fc n err)
    = pure $ hsep [ errorDesc (reflow "While processing constructor" <++> code (pretty0 !(prettyName n))) <+> dot
                  , !(perrorRaw err)
                  ]
perrorRaw (InLHS fc n err)
    = pure $ hsep [ errorDesc (reflow "While processing left hand side of" <++> code (pretty0 !(prettyName n))) <+> dot
                  , !(perrorRaw err)
                  ]
perrorRaw (InRHS fc n err)
    = pure $ hsep [ errorDesc (reflow "While processing right hand side of" <++> code (pretty0 !(prettyName n))) <+> dot
                  , !(perrorRaw err)
                  ]

perrorRaw (MaybeMisspelling err ns) = pure $ !(perrorRaw err) <+> case ns of
  (n ::: []) => reflow "Did you mean:" <++> code (pretty0 n) <+> "?"
  _ => let (xs, x) = Lib.unsnoc ns in
       reflow "Did you mean any of:"
       <++> concatWith (surround (comma <+> space)) (map (code . pretty0) xs)
       <+> comma <++> "or" <++> code (pretty0 x) <+> "?"
perrorRaw (WarningAsError warn) = pwarningRaw warn

export
perror : {auto c : Ref Ctxt Defs} ->
         {auto s : Ref Syn SyntaxInfo} ->
         {auto o : Ref ROpts REPLOpts} ->
         Error -> Core (Doc IdrisAnn)
perror err = perrorRaw !(toFullNames err)

||| Check (in a whitespace-insensitive manner) that the msg is
||| contained in the error.
export
checkError :
  {auto c : Ref Ctxt Defs} ->
  {auto s : Ref Syn SyntaxInfo} ->
  {auto o : Ref ROpts REPLOpts} ->
  (msg : String) -> Error -> Core Bool
checkError msg err = do
  -- Kill the locations so that we don't get source code excerpts
  let err = killErrorLoc err
  -- Show the error as a string
  str <- show <$> perror err
  -- Normalise the two strings. This ensures comparison is whitespace
  -- insentitive (error messages' layout depend on terminal width)
  let msg = unwords (words msg)
  let str = unwords (words str)
  pure (msg `isInfixOf` str)

prettyMaybeLoc : Maybe FC -> Doc IdrisAnn
prettyMaybeLoc Nothing = emptyDoc
prettyMaybeLoc (Just fc) = annotate FileCtxt (pretty0 fc) <+> colon

export
display : {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto o : Ref ROpts REPLOpts} ->
          Error -> Core (Doc IdrisAnn)
display err = do
  pure $ annotate Error "Error:" <++> !(perror err)

export
displayWarning : {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 Warning -> Core (Doc IdrisAnn)
displayWarning w
    = pure $ annotate Warning "Warning:" <++> !(pwarning w)
