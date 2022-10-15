module Core.Error

import Core.Binary
import public Core.Core
import public Core.Env
import public Core.Context.CtxtData
import public Core.TT
import public Core.Warning

import Data.List1
import System.File

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
               | MatchErased (vars ** (Env Term vars, Term vars))
               | NotFullyApplied Name
               | UnknownType

public export
data Error : Type where
     CantConvert : {vars : _} ->
                   FC -> Defs -> Env Term vars ->
                   Term vars -> Term vars -> Error
     CantSolveEq : {vars : _} ->
                   FC -> Defs -> Env Term vars -> Term vars -> Term vars -> Error
     WhenUnifying : {vars : _} ->
                    FC -> Defs -> Env Term vars -> Term vars -> Term vars -> Error -> Error

     UndefinedName : FC -> Name -> Error
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
     CaseCompile : FC -> Name -> CaseError -> Error

     LinearUsed : FC -> Nat -> Name -> Error
     LinearMisuse : FC -> Name -> RigCount -> RigCount -> Error

     AmbiguousName : FC -> List Name -> Error
     AmbiguousElab : {vars : _} ->
                     FC -> Env Term vars -> List (Defs, Term vars) -> Error
     AmbiguousSearch : {vars : _} ->
                       FC -> Env Term vars -> Term vars -> List (Term vars) -> Error
     AmbiguityTooDeep : FC -> Name -> List Name -> Error
     AllFailed : List (Maybe Name, Error) -> Error

     BadUnboundImplicit : {vars : _} ->
                          FC -> Env Term vars -> Name -> Term vars -> Error
     TryWithImplicits : {vars : _} ->
                        FC -> Env Term vars -> List (Name, Term vars) -> Error
     CantSolveGoal : {vars : _} ->
                     FC -> Defs -> Env Term vars -> Term vars ->
                     Maybe Error -> Error
     UnsolvedHoles : List (FC, Name) -> Error
     DeterminingArg : {vars : _} ->
                      FC -> Name -> Int -> Env Term vars -> Term vars -> Error

     MaybeMisspelling : Error -> List1 String -> Error
     ModuleNotFound : FC -> ModuleIdent -> Error

     GenericMsg : FC -> String -> Error
     UserError : String -> Error
     LitFail : FC -> Error
     LexFail : FC -> String -> Error
     ParseFail : List1 (FC, String) -> Error
     InternalError : String -> Error
     TTCErr : TTCError -> Error
     FileErr : TFileError -> Error

     InType : FC -> Name -> Error -> Error
     InCon : FC -> Name -> Error -> Error
     InLHS : FC -> Name -> Error -> Error
     InRHS : FC -> Name -> Error -> Error

     WarningAsError : Warning -> Error

-- Simplest possible display - higher level languages should unelaborate names
-- and display annotations appropriately

export
Show Error where
  show (CantConvert fc defs env x y)
      = show fc ++ ":Can't convert " ++ show x ++ " with " ++ show y
  show (CantSolveEq fc _ env x y)
      = show fc ++ ":" ++ show x ++ " and " ++ show y ++ " are not equal"
  show (WhenUnifying fc _ _ x y err)
      = show fc ++ ":When unifying: " ++ show x ++ " and " ++ show y ++ "\n\t" ++ show err

  show (UndefinedName fc n) = show fc ++ ":Undefined name " ++ show n
  show (NoDeclaration fc x) = show fc ++ ":No type declaration for " ++ show x
  show (BadTypeConType fc n)
       = show fc ++ ":Return type of " ++ show n ++ " must be Type"
  show (BadDataConType fc n fam)
       = show fc ++ ":Return type of " ++ show n ++ " must be in " ++ show fam
  show (BadDotPattern fc env reason x y)
      = show fc ++ ":Can't match on " ++ show x ++
           " (" ++ show reason ++ ")" ++
           " - it elaborates to " ++ show y

  show (AmbiguousName fc ns) = show fc ++ ":Ambiguous name " ++ show ns
  show (AmbiguousElab fc env ts) = show fc ++ ":Ambiguous elaboration " ++ show (map snd ts)
  show (AmbiguousSearch fc env tgt ts) = show fc ++ ":Ambiguous search " ++ show ts
  show (AmbiguityTooDeep fc n ns)
      = show fc ++ ":Ambiguity too deep in " ++ show n ++ " " ++ show ns
  show (AllFailed ts) = "No successful elaboration: " ++ assert_total (show ts)

  show (PatternVariableUnifies fc fct env n x)
      = show fc ++ ":Pattern variable " ++ show n ++ " unifies with " ++ show x
  show (CyclicMeta fc env n tm)
      = show fc ++ ":Cycle detected in metavariable solution " ++ show n
             ++ " = " ++ show tm

  show (AlreadyDefined fc n) = show fc ++ ":" ++ show n ++ " is already defined"
  show (NotFunctionType fc defs env t)
      = show fc ++ ":" ++ show t ++ " is not a function type"
  show (CaseCompile fc n DifferingArgNumbers)
      = show fc ++ ":Patterns for " ++ show n ++ " have different numbers of arguments"
  show (CaseCompile fc n DifferingTypes)
      = show fc ++ ":Patterns for " ++ show n ++ " require matching on different types"
  show (CaseCompile fc n UnknownType)
      = show fc ++ ":Can't infer type to match in " ++ show n
  show (CaseCompile fc n (MatchErased (_ ** (env, tm))))
      = show fc ++ ":Attempt to match on erased argument " ++ show tm ++
                   " in " ++ show n
  show (CaseCompile fc n (NotFullyApplied c))
      = show fc ++ ":Constructor " ++ show c ++ " is not fully applied"

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
  show (GenericMsg fc str) = show fc ++ ":" ++ str
  show (UserError str) = "Error: " ++ str

  show (LitFail fc) = show fc ++ ":Can't parse literate"
  show (LexFail fc err) = show fc ++ ":Lexer error (" ++ show err ++ ")"
  show (ParseFail errs) = "Parse errors (" ++ show errs ++ ")"
  show (InternalError str) = "INTERNAL ERROR: " ++ str

  show (TTCErr err) = "TTC error: " ++ show err
  show (FileErr err) = "File error: " ++ show err

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
