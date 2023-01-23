module Core.Error

import Core.Binary
import public Core.Core
import public Core.Env
import public Core.Context.CtxtData
import public Core.TT
import public Core.Warning

import Data.List
import Data.List1
import Data.String
import System.File

import Libraries.Utils.Shunting

-- All the core TTImp errors

public export
data TFileError : Type where
     SystemFileErr : String -> FileError -> TFileError
     TTFileErr : String -> TFileError

export
Show TFileError where
  show (SystemFileErr fname ferr)
      = show fname ++ ":" ++ show ferr
  show (TTFileErr str) = str

public export
data CaseError = DifferingArgNumbers
               | DifferingTypes
               | CantResolveType
               | MatchErased (vars ** (Env Term vars, Term vars))
               | NotFullyApplied Name
               | UnknownType

public export
data Error : Type where
     Fatal : Error -> Error -- flag as unrecoverable (so don't postpone awaiting further info)
     CantConvert : {vars : _} ->
                   FC -> Defs -> Env Term vars ->
                   Term vars -> Term vars -> Error
     CantSolveEq : {vars : _} ->
                   FC -> Defs -> Env Term vars -> Term vars -> Term vars -> Error
     WhenUnifying : {vars : _} ->
                    FC -> Defs -> Env Term vars -> Term vars -> Term vars -> Error -> Error
     ValidCase : {vars : _} ->
                 FC -> Env Term vars -> Either (Term vars) Error -> Error

     UndefinedName : FC -> Name -> Error
     InvisibleName : FC -> Name -> Maybe Namespace -> Error

     NonLinearPattern : FC -> Name -> Error
     BadPattern : FC -> Name -> Error

     NoDeclaration : FC -> Name -> Error
     BadTypeConType : FC -> Name -> Error
     BadDataConType : FC -> Name -> Name -> Error
     BadDotPattern : {vars : _} ->
                     FC -> Env Term vars -> DotReason -> Term vars -> Term vars -> Error

     PatternVariableUnifies : {vars : _} ->
                              FC -> FC -> Env Term vars -> Name -> Term vars -> Error
     CyclicMeta : {vars : _} ->
                  FC -> Env Term vars -> Name -> Term vars -> Error

     AlreadyDefined : FC -> Name -> Error
     NotFunctionType : {vars : _} ->
                   FC -> Defs -> Env Term vars ->
                   Term vars -> Error
     RewriteNoChange : {vars : _} ->
                       FC -> Env Term vars -> Term vars -> Term vars -> Error
     NotRewriteRule : {vars : _} ->
                      FC -> Env Term vars -> Term vars -> Error

     CaseCompile : FC -> Name -> CaseError -> Error
     MatchTooSpecific : {vars : _} ->
                        FC -> Env Term vars -> Term vars -> Error
     NotCovering : FC -> Name -> Covering -> Error
     NotTotal : FC -> Name -> PartialReason -> Error
     LinearUsed : FC -> Nat -> Name -> Error
     LinearMisuse : FC -> Name -> RigCount -> RigCount -> Error
     BorrowPartial : {vars : _} ->
                     FC -> Env Term vars -> Term vars -> Term vars -> Error
     BorrowPartialType : {vars : _} ->
                         FC -> Env Term vars -> Term vars -> Error

     AmbiguousName : FC -> List Name -> Error
     AmbiguousElab : {vars : _} ->
                     FC -> Env Term vars -> List (Defs, Term vars) -> Error
     AmbiguousSearch : {vars : _} ->
                       FC -> Env Term vars -> Term vars -> List (Term vars) -> Error
     AmbiguityTooDeep : FC -> Name -> List Name -> Error
     AllFailed : List (Maybe Name, Error) -> Error

     RecordTypeNeeded : {vars : _} ->
                        FC -> Env Term vars -> Error
     DuplicatedRecordUpdatePath : FC -> List (List String) -> Error
     NotRecordField : FC -> String -> Maybe Name -> Error
     NotRecordType : FC -> Name -> Error
     IncompatibleFieldUpdate : FC -> List String -> Error

     InvalidArgs : {vars : _} ->
                   FC -> Env Term vars -> List Name -> Term vars -> Error

     BadUnboundImplicit : {vars : _} ->
                          FC -> Env Term vars -> Name -> Term vars -> Error
     TryWithImplicits : {vars : _} ->
                        FC -> Env Term vars -> List (Name, Term vars) -> Error
     CantSolveGoal : {vars : _} ->
                     FC -> Defs -> Env Term vars -> Term vars ->
                     Maybe Error -> Error
     UnsolvedHoles : List (FC, Name) -> Error
     CantInferArgType : {vars : _} ->
                        FC -> Env Term vars -> Name -> Name -> Term vars -> Error
     SolvedNamedHole : {vars : _} ->
                       FC -> Env Term vars -> Name -> Term vars -> Error
     VisibilityError : FC -> Visibility -> Name -> Visibility -> Name -> Error

     DeterminingArg : {vars : _} ->
                      FC -> Name -> Int -> Env Term vars -> Term vars -> Error

     MaybeMisspelling : Error -> List1 String -> Error
     ModuleNotFound : FC -> ModuleIdent -> Error

     BadImplicit : FC -> String -> Error
     BadRunElab : {vars : _} ->
                  FC -> Env Term vars -> Term vars -> (description : String) -> Error
     RunElabFail : Error -> Error

     GenericMsg : FC -> String -> Error
     UserError : String -> Error
     CantFindPackage : String -> Error
     LitFail : FC -> Error
     LexFail : FC -> String -> Error
     ParseFail : List1 (FC, String) -> Error
     CyclicImports : List ModuleIdent -> Error
     ForceNeeded : Error
     InternalError : String -> Error
     TTCErr : TTCError -> Error
     FileErr : TFileError -> Error
     NoForeignCC : FC -> List String -> Error
     BadMultiline : FC -> String -> Error
     Timeout : String -> Error
     FailingDidNotFail : FC -> Error
     FailingWrongError : FC -> String -> List1 Error -> Error

     InType : FC -> Name -> Error -> Error
     InCon : FC -> Name -> Error -> Error
     InLHS : FC -> Name -> Error -> Error
     InRHS : FC -> Name -> Error -> Error

     WarningAsError : Warning -> Error

export
getWarningLoc : Warning -> Maybe FC
getWarningLoc (ParserWarning fc _) = Just fc
getWarningLoc (UnreachableClause fc _ _) = Just fc
getWarningLoc (ShadowingGlobalDefs fc _) = Just fc
getWarningLoc (ShadowingLocalBindings fc _) = Just fc
getWarningLoc (Deprecated _ fcAndName) = fst <$> fcAndName
getWarningLoc (GenericWarn _) = Nothing

export
getErrorLoc : Error -> Maybe FC
getErrorLoc (Fatal err) = getErrorLoc err
getErrorLoc (CantConvert loc _ _ _ _) = Just loc
getErrorLoc (CantSolveEq loc _ _ _ _) = Just loc
getErrorLoc (PatternVariableUnifies loc _ _ _ _) = Just loc
getErrorLoc (CyclicMeta loc _ _ _) = Just loc
getErrorLoc (WhenUnifying loc _ _ _ _ _) = Just loc
getErrorLoc (ValidCase loc _ _) = Just loc
getErrorLoc (UndefinedName loc _) = Just loc
getErrorLoc (InvisibleName loc _ _) = Just loc
getErrorLoc (BadTypeConType loc _) = Just loc
getErrorLoc (BadDataConType loc _ _) = Just loc
getErrorLoc (NotCovering loc _ _) = Just loc
getErrorLoc (NotTotal loc _ _) = Just loc
getErrorLoc (LinearUsed loc _ _) = Just loc
getErrorLoc (LinearMisuse loc _ _ _) = Just loc
getErrorLoc (BorrowPartial loc _ _ _) = Just loc
getErrorLoc (BorrowPartialType loc _ _) = Just loc
getErrorLoc (AmbiguousName loc _) = Just loc
getErrorLoc (AmbiguousElab loc _ _) = Just loc
getErrorLoc (AmbiguousSearch loc _ _ _) = Just loc
getErrorLoc (AmbiguityTooDeep loc _ _) = Just loc
getErrorLoc (AllFailed ((_, x) :: _)) = getErrorLoc x
getErrorLoc (AllFailed []) = Nothing
getErrorLoc (RecordTypeNeeded loc _) = Just loc
getErrorLoc (DuplicatedRecordUpdatePath loc _) = Just loc
getErrorLoc (NotRecordField loc _ _) = Just loc
getErrorLoc (NotRecordType loc _) = Just loc
getErrorLoc (IncompatibleFieldUpdate loc _) = Just loc
getErrorLoc (InvalidArgs loc _ _ _) = Just loc
getErrorLoc (TryWithImplicits loc _ _) = Just loc
getErrorLoc (BadUnboundImplicit loc _ _ _) = Just loc
getErrorLoc (CantSolveGoal loc _ _ _ _) = Just loc
getErrorLoc (DeterminingArg loc _ _ _ _) = Just loc
getErrorLoc (UnsolvedHoles ((loc, _) :: _)) = Just loc
getErrorLoc (UnsolvedHoles []) = Nothing
getErrorLoc (CantInferArgType loc _ _ _ _) = Just loc
getErrorLoc (SolvedNamedHole loc _ _ _) = Just loc
getErrorLoc (VisibilityError loc _ _ _ _) = Just loc
getErrorLoc (NonLinearPattern loc _) = Just loc
getErrorLoc (BadPattern loc _) = Just loc
getErrorLoc (NoDeclaration loc _) = Just loc
getErrorLoc (AlreadyDefined loc _) = Just loc
getErrorLoc (NotFunctionType loc _ _ _) = Just loc
getErrorLoc (RewriteNoChange loc _ _ _) = Just loc
getErrorLoc (NotRewriteRule loc _ _) = Just loc
getErrorLoc (CaseCompile loc _ _) = Just loc
getErrorLoc (MatchTooSpecific loc _ _) = Just loc
getErrorLoc (BadDotPattern loc _ _ _ _) = Just loc
getErrorLoc (BadImplicit loc _) = Just loc
getErrorLoc (BadRunElab loc _ _ _) = Just loc
getErrorLoc (RunElabFail e) = getErrorLoc e
getErrorLoc (GenericMsg loc _) = Just loc
getErrorLoc (TTCErr _) = Nothing
getErrorLoc (FileErr _) = Nothing
getErrorLoc (CantFindPackage _) = Nothing
getErrorLoc (LitFail loc) = Just loc
getErrorLoc (LexFail loc _) = Just loc
getErrorLoc (ParseFail ((loc, _) ::: _)) = Just loc
getErrorLoc (ModuleNotFound loc _) = Just loc
getErrorLoc (CyclicImports _) = Nothing
getErrorLoc ForceNeeded = Nothing
getErrorLoc (InternalError _) = Nothing
getErrorLoc (UserError _) = Nothing
getErrorLoc (NoForeignCC loc _) = Just loc
getErrorLoc (BadMultiline loc _) = Just loc
getErrorLoc (Timeout _) = Nothing
getErrorLoc (InType _ _ err) = getErrorLoc err
getErrorLoc (InCon _ _ err) = getErrorLoc err
getErrorLoc (FailingDidNotFail fc) = pure fc
getErrorLoc (FailingWrongError fc _ _) = pure fc
getErrorLoc (InLHS _ _ err) = getErrorLoc err
getErrorLoc (InRHS _ _ err) = getErrorLoc err
getErrorLoc (MaybeMisspelling err _) = getErrorLoc err
getErrorLoc (WarningAsError warn) = getWarningLoc warn

export
killWarningLoc : Warning -> Warning
killWarningLoc (ParserWarning fc x) = ParserWarning emptyFC x
killWarningLoc (UnreachableClause fc x y) = UnreachableClause emptyFC x y
killWarningLoc (ShadowingGlobalDefs fc xs) = ShadowingGlobalDefs emptyFC xs
killWarningLoc (ShadowingLocalBindings fc xs) =
    ShadowingLocalBindings emptyFC $ (\(n, _, _) => (n, emptyFC, emptyFC)) <$> xs
killWarningLoc (Deprecated x y) = Deprecated x (map ((emptyFC,) . snd) y)
killWarningLoc (GenericWarn x) = GenericWarn x

export
killErrorLoc : Error -> Error
killErrorLoc (Fatal err) = Fatal (killErrorLoc err)
killErrorLoc (CantConvert fc x y z w) = CantConvert emptyFC x y z w
killErrorLoc (CantSolveEq fc x y z w) = CantSolveEq emptyFC x y z w
killErrorLoc (PatternVariableUnifies fc fct x y z) = PatternVariableUnifies emptyFC emptyFC x y z
killErrorLoc (CyclicMeta fc x y z) = CyclicMeta emptyFC x y z
killErrorLoc (WhenUnifying fc x y z w err) = WhenUnifying emptyFC x y z w (killErrorLoc err)
killErrorLoc (ValidCase fc x y) = ValidCase emptyFC x y
killErrorLoc (UndefinedName fc x) = UndefinedName emptyFC x
killErrorLoc (InvisibleName fc x y) = InvisibleName emptyFC x y
killErrorLoc (BadTypeConType fc x) = BadTypeConType emptyFC x
killErrorLoc (BadDataConType fc x y) = BadDataConType emptyFC x y
killErrorLoc (NotCovering fc x y) = NotCovering emptyFC x y
killErrorLoc (NotTotal fc x y) = NotTotal emptyFC x y
killErrorLoc (LinearUsed fc k x) = LinearUsed emptyFC k x
killErrorLoc (LinearMisuse fc x y z) = LinearMisuse emptyFC x y z
killErrorLoc (BorrowPartial fc x y z) = BorrowPartial emptyFC x y z
killErrorLoc (BorrowPartialType fc x y) = BorrowPartialType emptyFC x y
killErrorLoc (AmbiguousName fc xs) = AmbiguousName emptyFC xs
killErrorLoc (AmbiguousElab fc x xs) = AmbiguousElab emptyFC x xs
killErrorLoc (AmbiguousSearch fc x y xs) = AmbiguousSearch emptyFC x y xs
killErrorLoc (AmbiguityTooDeep fc x xs) = AmbiguityTooDeep emptyFC x xs
killErrorLoc (AllFailed xs) = AllFailed (map (map killErrorLoc) xs)
killErrorLoc (RecordTypeNeeded fc x) = RecordTypeNeeded emptyFC x
killErrorLoc (DuplicatedRecordUpdatePath fc xs) = DuplicatedRecordUpdatePath emptyFC xs
killErrorLoc (NotRecordField fc x y) = NotRecordField emptyFC x y
killErrorLoc (NotRecordType fc x) = NotRecordType emptyFC x
killErrorLoc (IncompatibleFieldUpdate fc xs) = IncompatibleFieldUpdate emptyFC xs
killErrorLoc (InvalidArgs fc x xs y) = InvalidArgs emptyFC x xs y
killErrorLoc (TryWithImplicits fc x xs) = TryWithImplicits emptyFC x xs
killErrorLoc (BadUnboundImplicit fc x y z) = BadUnboundImplicit emptyFC x y z
killErrorLoc (CantSolveGoal fc x y z w) = CantSolveGoal emptyFC x y z w
killErrorLoc (DeterminingArg fc x y z w) = DeterminingArg emptyFC x y z w
killErrorLoc (UnsolvedHoles xs) = UnsolvedHoles xs
killErrorLoc (CantInferArgType fc x y z w) = CantInferArgType emptyFC x y z w
killErrorLoc (SolvedNamedHole fc x y z) = SolvedNamedHole emptyFC x y z
killErrorLoc (VisibilityError fc x y z w) = VisibilityError emptyFC x y z w
killErrorLoc (NonLinearPattern fc x) = NonLinearPattern emptyFC x
killErrorLoc (BadPattern fc x) = BadPattern emptyFC x
killErrorLoc (NoDeclaration fc x) = NoDeclaration emptyFC x
killErrorLoc (AlreadyDefined fc x) = AlreadyDefined emptyFC x
killErrorLoc (NotFunctionType fc x y z) = NotFunctionType emptyFC x y z
killErrorLoc (RewriteNoChange fc x y z) = RewriteNoChange emptyFC x y z
killErrorLoc (NotRewriteRule fc x y) = NotRewriteRule emptyFC x y
killErrorLoc (CaseCompile fc x y) = CaseCompile emptyFC x y
killErrorLoc (MatchTooSpecific fc x y) = MatchTooSpecific emptyFC x y
killErrorLoc (BadDotPattern fc x y z w) = BadDotPattern emptyFC x y z w
killErrorLoc (BadImplicit fc x) = BadImplicit emptyFC x
killErrorLoc (BadRunElab fc x y description) = BadRunElab emptyFC x y description
killErrorLoc (RunElabFail e) = RunElabFail $ killErrorLoc e
killErrorLoc (GenericMsg fc x) = GenericMsg emptyFC x
killErrorLoc (TTCErr x) = TTCErr x
killErrorLoc (FileErr x) = FileErr x
killErrorLoc (CantFindPackage x) = CantFindPackage x
killErrorLoc (LitFail fc) = LitFail emptyFC
killErrorLoc (LexFail fc x) = LexFail emptyFC x
killErrorLoc (ParseFail xs) = ParseFail $ map ((emptyFC,) . snd) $ xs
killErrorLoc (ModuleNotFound fc x) = ModuleNotFound emptyFC x
killErrorLoc (CyclicImports xs) = CyclicImports xs
killErrorLoc ForceNeeded = ForceNeeded
killErrorLoc (InternalError x) = InternalError x
killErrorLoc (UserError x) = UserError x
killErrorLoc (NoForeignCC fc xs) = NoForeignCC emptyFC xs
killErrorLoc (BadMultiline fc x) = BadMultiline emptyFC x
killErrorLoc (Timeout x) = Timeout x
killErrorLoc (FailingDidNotFail fc) = FailingDidNotFail emptyFC
killErrorLoc (FailingWrongError fc x errs) = FailingWrongError emptyFC x (map killErrorLoc errs)
killErrorLoc (InType fc x err) = InType emptyFC x (killErrorLoc err)
killErrorLoc (InCon fc x err) = InCon emptyFC x (killErrorLoc err)
killErrorLoc (InLHS fc x err) = InLHS emptyFC x (killErrorLoc err)
killErrorLoc (InRHS fc x err) = InRHS emptyFC x (killErrorLoc err)
killErrorLoc (MaybeMisspelling err xs) = MaybeMisspelling (killErrorLoc err) xs
killErrorLoc (WarningAsError wrn) = WarningAsError (killWarningLoc wrn)

-- Simplest possible display - higher level languages should unelaborate names
-- and display annotations appropriately

export
Show Error where
  show (Fatal err) = show err
  show (CantConvert fc defs env x y)
      = show fc ++ ":Can't convert " ++ show x ++ " with " ++ show y
  show (CantSolveEq fc _ env x y)
      = show fc ++ ":" ++ show x ++ " and " ++ show y ++ " are not equal"
  show (WhenUnifying fc _ _ x y err)
      = show fc ++ ":When unifying: " ++ show x ++ " and " ++ show y ++ "\n\t" ++ show err
  show (ValidCase fc _ prob)
      = show fc ++ ":" ++
           case prob of
             Left tm => assert_total (show tm) ++ " is not a valid impossible pattern because it typechecks"
             Right err => "Not a valid impossible pattern:\n\t" ++ assert_total (show err)

  show (UndefinedName fc n) = show fc ++ ":Undefined name " ++ show n
  show (InvisibleName fc x (Just ns))
       = show fc ++ ":Name " ++ show x ++ " is inaccessible since " ++
         show ns ++ " is not explicitly imported"
  show (InvisibleName fc x _) = show fc ++ ":Name " ++ show x ++ " is private"
  show (NoDeclaration fc x) = show fc ++ ":No type declaration for " ++ show x
  show (BadTypeConType fc n)
       = show fc ++ ":Return type of " ++ show n ++ " must be Type"
  show (BadDataConType fc n fam)
       = show fc ++ ":Return type of " ++ show n ++ " must be in " ++ show fam
  show (BadDotPattern fc env reason x y)
      = show fc ++ ":Can't match on " ++ show x ++
           " (" ++ show reason ++ ")" ++
           " - it elaborates to " ++ show y
  show (BorrowPartial fc env t arg)
      = show fc ++ ":" ++ show t ++ " borrows argument " ++ show arg ++
                   " so must be fully applied"
  show (BorrowPartialType fc env t)
      = show fc ++ ":" ++ show t ++ " borrows, so must return a concrete type"
  show (AmbiguousName fc ns) = show fc ++ ":Ambiguous name " ++ show ns
  show (AmbiguousElab fc env ts) = show fc ++ ":Ambiguous elaboration " ++ show (map snd ts)
  show (AmbiguousSearch fc env tgt ts) = show fc ++ ":Ambiguous search " ++ show ts
  show (AmbiguityTooDeep fc n ns)
      = show fc ++ ":Ambiguity too deep in " ++ show n ++ " " ++ show ns
  show (AllFailed ts) = "No successful elaboration: " ++ assert_total (show ts)

  show (RecordTypeNeeded fc env)
      = show fc ++ ":Can't infer type of record to update"
  show (DuplicatedRecordUpdatePath fc ps)
      = show fc ++ ":Duplicated record update paths: " ++ show ps
  show (NotRecordField fc fld Nothing)
      = show fc ++ ":" ++ fld ++ " is not part of a record type"
  show (NotRecordField fc fld (Just ty))
      = show fc ++ ":Record type " ++ show ty ++ " has no field " ++ fld
  show (NotRecordType fc ty)
      = show fc ++ ":" ++ show ty ++ " is not a record type"
  show (IncompatibleFieldUpdate fc flds)
      = show fc ++ ":Field update " ++ showSep "->" flds ++ " not compatible with other updates"

  show (InvalidArgs fc env ns tm)
     = show fc ++ ":" ++ show ns ++ " are not valid arguments in " ++ show tm

  show (PatternVariableUnifies fc fct env n x)
      = show fc ++ ":Pattern variable " ++ show n ++ " unifies with " ++ show x
  show (CyclicMeta fc env n tm)
      = show fc ++ ":Cycle detected in metavariable solution " ++ show n
             ++ " = " ++ show tm
  show (CantInferArgType fc env n h ty)
      = show fc ++ ":Can't infer type for " ++ show n ++
                   " (got " ++ show ty ++ " with hole " ++ show h ++ ")"
  show (SolvedNamedHole fc _ h _) = show fc ++ ":Named hole " ++ show h ++ " is solved by unification"
  show (VisibilityError fc vx x vy y)
      = show fc ++ ":" ++ show vx ++ " " ++ show x ++ " cannot refer to "
                       ++ show vy ++ " " ++ show y
  show (NonLinearPattern fc n) = show fc ++ ":Non linear pattern variable " ++ show n
  show (BadPattern fc n) = show fc ++ ":Pattern not allowed here: " ++ show n

  show (AlreadyDefined fc n) = show fc ++ ":" ++ show n ++ " is already defined"
  show (NotFunctionType fc defs env t)
      = show fc ++ ":" ++ show t ++ " is not a function type"
  show (RewriteNoChange fc env rule ty)
      = show fc ++ ":Rewriting by " ++ show rule ++ " did not change type " ++ show ty
  show (NotRewriteRule fc env rule)
      = show fc ++ ":" ++ show rule ++ " is not a rewrite rule type"

  show (CaseCompile fc n DifferingArgNumbers)
      = show fc ++ ":Patterns for " ++ show n ++ " have different numbers of arguments"
  show (CaseCompile fc n DifferingTypes)
      = show fc ++ ":Patterns for " ++ show n ++ " require matching on different types"
  show (CaseCompile fc n CantResolveType)
      = show fc ++ ":Can't resolve argument types in patterns for " ++ show n
  show (CaseCompile fc n UnknownType)
      = show fc ++ ":Can't infer type to match in " ++ show n
  show (CaseCompile fc n (MatchErased (_ ** (env, tm))))
      = show fc ++ ":Attempt to match on erased argument " ++ show tm ++
                   " in " ++ show n
  show (CaseCompile fc n (NotFullyApplied c))
      = show fc ++ ":Constructor " ++ show c ++ " is not fully applied"
  show (MatchTooSpecific fc env tm)
      = show fc ++ ":Can't match on " ++ show tm ++ " as it has a polymorphic type"
  show (NotCovering fc n cov)
       = show fc ++ ":" ++ show n ++ " is not covering:\n\t" ++
            case cov of
                 IsCovering => "Oh yes it is (Internal error!)"
                 MissingCases cs => "Missing cases:\n\t" ++
                                           showSep "\n\t" (map show cs)
                 NonCoveringCall ns => "Calls non covering function"
                                           ++ (case ns of
                                                   [fn] => " " ++ show fn
                                                   _ => "s: " ++ showSep ", " (map show ns))

  show (NotTotal fc n r)
       = show fc ++ ":" ++ show n ++ " is not total"
  show (LinearUsed fc count n)
      = show fc ++ ":There are " ++ show count ++ " uses of linear name " ++ show n
  show (LinearMisuse fc n exp ctx)
      = show fc ++ ":Trying to use " ++ showRig exp ++ " name " ++ show n ++
                   " in " ++ showRel ctx ++ " context"
     where
       showRig : RigCount -> String
       showRig = elimSemi
         "irrelevant"
         "linear"
         (const "unrestricted")

       showRel : RigCount -> String
       showRel = elimSemi
         "irrelevant"
         "relevant"
         (const "non-linear")
  show (BadUnboundImplicit fc env n ty)
      = show fc ++ ":Can't bind name " ++ nameRoot n ++
                   " with type " ++ show ty
  show (TryWithImplicits fc env imps)
     = show fc ++ ":Need to bind implicits "
          ++ showSep "," (map (\x => show (fst x) ++ " : " ++ show (snd x)) imps)
          ++ "\n(The front end should probably have done this for you. Please report!)"
  show (CantSolveGoal fc gam env g cause)
      = show fc ++ ":Can't solve goal " ++ assert_total (show g)
  show (DeterminingArg fc n i env g)
      = show fc ++ ":Can't solve goal " ++ assert_total (show g) ++
                " since argument " ++ show n ++ " can't be inferred"

  show (UnsolvedHoles hs) = "Unsolved holes " ++ show hs
  show (MaybeMisspelling err ns)
     = show err ++ "\nDid you mean" ++ case ns of
         (n ::: []) => ": " ++ n ++ "?"
         _ => " any of: " ++ showSep ", " (map show (forget ns)) ++ "?"
  show (ModuleNotFound fc ns)
      = show fc ++ ":" ++ show ns ++ " not found"
  show (BadImplicit fc str) = show fc ++ ":" ++ str ++ " can't be bound here"
  show (BadRunElab fc env script desc) = show fc ++ ":Bad elaborator script " ++ show script ++ " (" ++ desc ++ ")"
  show (RunElabFail e) = "Error during reflection: " ++ show e
  show (GenericMsg fc str) = show fc ++ ":" ++ str
  show (UserError str) = "Error: " ++ str
  show (CantFindPackage fname) = "Can't find package " ++ fname
  show (LitFail fc) = show fc ++ ":Can't parse literate"
  show (LexFail fc err) = show fc ++ ":Lexer error (" ++ show err ++ ")"
  show (ParseFail errs) = "Parse errors (" ++ show errs ++ ")"
  show (CyclicImports ns)
      = "Module imports form a cycle: " ++ showSep " -> " (map show ns)
  show ForceNeeded = "Internal error when resolving implicit laziness"
  show (InternalError str) = "INTERNAL ERROR: " ++ str
  show (TTCErr err) = "TTC error: " ++ show err
  show (FileErr err) = "File error: " ++ show err
  show (NoForeignCC fc specs) = show fc ++
       ":The given specifier " ++ show specs ++ " was not accepted by any available backend."
  show (BadMultiline fc str) = "Invalid multiline string: " ++ str
  show (Timeout str) = "Timeout in " ++ str
  show (FailingDidNotFail _) = "Failing block did not fail"
  show (FailingWrongError fc msg err)
       = assert_total $
         show fc ++ ":Failing block failed with the wrong error:\n" ++
         "Expected: " ++ msg ++ "\n" ++
         "but got: " ++ show err

  show (InType fc n err)
       = show fc ++ ":When elaborating type of " ++ show n ++ ":\n" ++
         show err
  show (InCon fc n err)
       = show fc ++ ":When elaborating type of constructor " ++ show n ++ ":\n" ++
         show err
  show (InLHS fc n err)
       = show fc ++ ":When elaborating left hand side of " ++ show n ++ ":\n" ++
         show err
  show (InRHS fc n err)
       = show fc ++ ":When elaborating right hand side of " ++ show n ++ ":\n" ++
         show err

  show (WarningAsError w) = show w

export
checkError :
  {auto c : Ref Ctxt Defs} ->
  (msg : String) -> Error -> CoreE Error Bool
checkError msg err = do
  -- Kill the locations so that we don't get source code excerpts
  let err = killErrorLoc err
  -- Show the error as a string
  let str = show err
  -- Normalise the two strings. This ensures comparison is whitespace
  -- insentitive (error messages' layout depend on terminal width)
  let msg = unwords (words msg)
  let str = unwords (words str)
  pure (msg `isInfixOf` str)

public export
Core : Type -> Type
Core = CoreE Error

public export
CoreFile : Type -> Type
CoreFile = CoreE TFileError

export
ttc : CoreTTC a -> Core a
ttc = wrap TTCErr

export
file : CoreFile a -> Core a
file = wrap FileErr

export
shunt : FC -> CoreSh a -> Core a
shunt fc = wrap (\err => GenericMsg fc (show err))

export
writeFile : (fname : String) -> (content : String) -> CoreFile ()
writeFile fname content =
  coreLift (writeFile fname content) >>= \case
    Right () => pure ()
    Left err => throw $ SystemFileErr fname err

export
readFile : (fname : String) -> CoreFile String
readFile fname =
  coreLift (readFile fname) >>= \case
    Right content => pure content
    Left err => throw $ SystemFileErr fname err

export
Eq FileError where
  GenericFileError x1 == GenericFileError x2 = x1 == x2
  FileReadError == FileReadError = True
  FileWriteError == FileWriteError = True
  FileNotFound == FileNotFound = True
  PermissionDenied == PermissionDenied = True
  FileExists == FileExists = True
  _ == _ = False

export
Eq TFileError where
   SystemFileErr s err == SystemFileErr s' err' = s == s' && err == err'
   TTFileErr s == TTFileErr s' = s == s'
   _ == _ = False

-- Not fully correct, see e.g. `CantConvert` where we don't check the Env
export
Eq Error where
  Fatal err1 == Fatal err2 = err1 == err2
  CantConvert fc1 gam1 rho1 s1 t1 == CantConvert fc2 gam2 rho2 s2 t2 = fc1 == fc2
  CantSolveEq fc1 gam1 rho s1 t1 == CantSolveEq fc2 gam2 rho2 s2 t2 = fc1 == fc2
  PatternVariableUnifies fc1 fct1 rho1 n1 s1 == PatternVariableUnifies fc2 fct2 rho2 n2 s2 = fc1 == fc2 && fct1 == fct2 && n1 == n2
  CyclicMeta fc1 rho1 n1 s1 == CyclicMeta fc2 rho2 n2 s2 = fc1 == fc2 && n1 == n2
  WhenUnifying fc1 gam1 rho1 s1 t1 err1 == WhenUnifying fc2 gam2 rho2 s2 t2 err2 = fc1 == fc2 && err1 == err2
  ValidCase fc1 rho1 x1 == ValidCase fc2 rho2 x2 = fc1 == fc2
  UndefinedName fc1 n1 == UndefinedName fc2 n2 = fc1 == fc2 && n1 == n2
  InvisibleName fc1 n1 x1 == InvisibleName fc2 n2 x2 = fc1 == fc2 && n1 == n2 && x1 == x2
  BadTypeConType fc1 n1 == BadTypeConType fc2 n2 = fc1 == fc2 && n1 == n2
  BadDataConType fc1 n1 m1 == BadDataConType fc2 n2 m2 = fc1 == fc2 && n1 == n2 && m1 == m2
  NotCovering fc1 n1 x1 == NotCovering fc2 n2 x2 = fc1 == fc2 && n1 == n2
  NotTotal fc1 n1 x1 == NotTotal fc2 n2 x2 = fc1 == fc2 && n1 == n2
  LinearUsed fc1 k1 n1 == LinearUsed fc2 k2 n2 = fc1 == fc2 && k1 == k2 && n1 == n2
  LinearMisuse fc1 n1 x1 y1 == LinearMisuse fc2 n2 x2 y2 = fc1 == fc2 && n1 == n2 && x1 == x2 && y1 == y2
  BorrowPartial fc1 rho1 s1 t1 == BorrowPartial fc2 rho2 s2 t2 = fc1 == fc2
  BorrowPartialType fc1 rho1 s1 == BorrowPartialType fc2 rho2 s2 = fc1 == fc2
  AmbiguousName fc1 xs1 == AmbiguousName fc2 xs2 = fc1 == fc2 && xs1 == xs2
  AmbiguousElab fc1 rho1 xs1 == AmbiguousElab fc2 rho2 xs2 = fc1 == fc2
  AmbiguousSearch fc1 rho1 s1 xs1 == AmbiguousSearch fc2 rho2 s2 xs2 = fc1 == fc2
  AmbiguityTooDeep fc1 n1 xs1 == AmbiguityTooDeep fc2 n2 xs2 = fc1 == fc2 && n1 == n2 && xs1 == xs2
  AllFailed xs1 == AllFailed xs2 = assert_total (xs1 == xs2)
  RecordTypeNeeded fc1 rho1 == RecordTypeNeeded fc2 rho2 = fc1 == fc2
  DuplicatedRecordUpdatePath fc1 xs1 == DuplicatedRecordUpdatePath fc2 xs2 = fc1 == fc2 && xs1 == xs2
  NotRecordField fc1 x1 y1 == NotRecordField fc2 x2 y2 = fc1 == fc2 && x1 == x2 && y1 == y2
  NotRecordType fc1 n1 == NotRecordType fc2 n2 = fc1 == fc2 && n1 == n2
  IncompatibleFieldUpdate fc1 xs1 == IncompatibleFieldUpdate fc2 xs2 = fc1 == fc2 && xs1 == xs2
  InvalidArgs fc1 rho1 xs1 s1 == InvalidArgs fc2 rho2 xs2 s2 = fc1 == fc2
  TryWithImplicits fc1 rho1 xs1 == TryWithImplicits fc2 rho2 xs2 = fc1 == fc2
  BadUnboundImplicit fc1 rho1 n1 s1 == BadUnboundImplicit fc2 rho2 n2 s2 = fc1 == fc2 && n1 == n2
  CantSolveGoal fc1 gam1 rho1 s1 x1 == CantSolveGoal fc2 gam2 rho2 s2 x2 = fc1 == fc2
  DeterminingArg fc1 n1 x1 rho1 s1 == DeterminingArg fc2 n2 x2 rho2 s2 = fc1 == fc2 && n1 == n2 && x1 == x2
  UnsolvedHoles xs1 == UnsolvedHoles xs2 = xs1 == xs2
  CantInferArgType fc1 rho1 n1 m1 s1 == CantInferArgType fc2 rho2 n2 m2 s2 = fc1 == fc2 && n1 == n2 && m1 == m2
  SolvedNamedHole fc1 rho1 n1 s1 == SolvedNamedHole fc2 rho2 n2 s2 = fc1 == fc2 && n1 == n2
  VisibilityError fc1 x1 n1 y1 m1 == VisibilityError fc2 x2 n2 y2 m2
    = fc1 == fc2 && x1 == x2 && n1 == n2 && y1 == y2 && m1 == m2
  NonLinearPattern fc1 n1 == NonLinearPattern fc2 n2 = fc1 == fc2 && n1 == n2
  BadPattern fc1 n1 == BadPattern fc2 n2 =  fc1 == fc2 && n1 == n2
  NoDeclaration fc1 n1 == NoDeclaration fc2 n2 = fc1 == fc2 && n1 == n2
  AlreadyDefined fc1 n1 == AlreadyDefined fc2 n2 = fc1 == fc2 && n1 == n2
  NotFunctionType fc1 rho1 s1 t1 == NotFunctionType fc2 rho2 s2 t2 = fc1 == fc2
  RewriteNoChange fc1 rho1 s1 t1 == RewriteNoChange fc2 rho2 s2 t2 = fc1 == fc2
  NotRewriteRule fc1 rho1 s1 == NotRewriteRule fc2 rho2 s2 = fc1 == fc2
  CaseCompile fc1 n1 x1 == CaseCompile fc2 n2 x2 = fc1 == fc2 && n1 == n2
  MatchTooSpecific fc1 rho1 s1 == MatchTooSpecific fc2 rho2 s2 = fc1 == fc2
  BadDotPattern fc1 rho1 x1 s1 t1 == BadDotPattern fc2 rho2 x2 s2 t2 = fc1 == fc2
  BadImplicit fc1 x1 == BadImplicit fc2 x2 = fc1 == fc2 && x1 == x2
  BadRunElab fc1 rho1 s1 d1 == BadRunElab fc2 rho2 s2 d2 = fc1 == fc2 && d1 == d2
  RunElabFail e1 == RunElabFail e2 = e1 == e2
  GenericMsg fc1 x1 == GenericMsg fc2 x2 = fc1 == fc2 && x1 == x2
  TTCErr x1 == TTCErr x2 = x1 == x2
  FileErr x1 == FileErr x2 = x1 == x2
  CantFindPackage x1 == CantFindPackage x2 = x1 == x2
  LitFail fc1 == LitFail fc2 = fc1 == fc2
  LexFail fc1 x1 == LexFail fc2 x2 = fc1 == fc2 && x1 == x2
  ParseFail xs1 == ParseFail xs2 = xs1 == xs2
  ModuleNotFound fc1 x1 == ModuleNotFound fc2 x2 = fc1 == fc2 && x1 == x2
  CyclicImports xs1 == CyclicImports xs2 = xs1 == xs2
  ForceNeeded == ForceNeeded = True
  InternalError x1 == InternalError x2 = x1 == x2
  UserError x1 == UserError x2 = x1 == x2
  NoForeignCC fc1 xs1 == NoForeignCC fc2 xs2 = fc1 == fc2 && xs1 == xs2
  BadMultiline fc1 x1 == BadMultiline fc2 x2 = fc1 == fc2 && x1 == x2
  Timeout x1 == Timeout x2 = x1 == x2
  FailingDidNotFail fc1 == FailingDidNotFail fc2 = fc1 == fc2
  FailingWrongError fc1 x1 err1 == FailingWrongError fc2 x2 err2
    = fc1 == fc2 && x1 == x2 && assert_total (err1 == err2)
  InType fc1 n1 err1 == InType fc2 n2 err2 = fc1 == fc2 && n1 == n2 && err1 == err2
  InCon fc1 n1 err1 == InCon fc2 n2 err2 = fc1 == fc2 && n1 == n2 && err1 == err2
  InLHS fc1 n1 err1 == InLHS fc2 n2 err2 = fc1 == fc2 && n1 == n2 && err1 == err2
  InRHS fc1 n1 err1 == InRHS fc2 n2 err2 = fc1 == fc2 && n1 == n2 && err1 == err2
  MaybeMisspelling err1 xs1 == MaybeMisspelling err2 xs2 = err1 == err2 && xs1 == xs2
  WarningAsError wrn1 == WarningAsError wrn2 = wrn1 == wrn2
  _ == _ = False
