module Core.Error

import Core.Binary
import public Core.Core
import public Core.Env
import public Core.Context.CtxtData
import public Core.TT

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
data Error : Type where
     UndefinedName : FC -> Name -> Error
     NoDeclaration : FC -> Name -> Error
     BadTypeConType : FC -> Name -> Error
     BadDataConType : FC -> Name -> Name -> Error

     AmbiguousName : FC -> List Name -> Error

     CantConvert : {vars : _} ->
                   FC -> Defs -> Env Term vars ->
                   Term vars -> Term vars -> Error
     AlreadyDefined : FC -> Name -> Error
     NotFunctionType : {vars : _} ->
                   FC -> Defs -> Env Term vars ->
                   Term vars -> Error
     LinearMisuse : FC -> Name -> RigCount -> RigCount -> Error

     MaybeMisspelling : Error -> List1 String -> Error
     ModuleNotFound : FC -> ModuleIdent -> Error
     GenericMsg : FC -> String -> Error
     UserError : String -> Error
     LexFail : FC -> String -> Error
     ParseFail : List1 (FC, String) -> Error
     InternalError : String -> Error
     TTCErr : TTCError -> Error
     FileErr : TFileError -> Error

export
Show Error where
  show (UndefinedName fc n) = show fc ++ ":Undefined name " ++ show n
  show (NoDeclaration fc x) = show fc ++ ":No type declaration for " ++ show x
  show (BadTypeConType fc n)
       = show fc ++ ":Return type of " ++ show n ++ " must be Type"
  show (BadDataConType fc n fam)
       = show fc ++ ":Return type of " ++ show n ++ " must be in " ++ show fam

  show (AmbiguousName fc ns) = show fc ++ ":Ambiguous name " ++ show ns

  show (CantConvert fc defs env x y)
      = show fc ++ ":Can't convert " ++ show x ++ " with " ++ show y
  show (AlreadyDefined fc n) = show fc ++ ":" ++ show n ++ " is already defined"
  show (NotFunctionType fc defs env t)
      = show fc ++ ":" ++ show t ++ " is not a function type"
  show (LinearMisuse fc n exp ctx)
      = show fc ++ ":Trying to use " ++ showRig exp ++ " name " ++ show n ++
                   " in " ++ showRel ctx ++ " context"
     where
       showRig : RigCount -> String
       showRig = elimSemi
         "linear"
         "irrelevant"
         (const "unrestricted")

       showRel : RigCount -> String
       showRel = elimSemi
         "relevant"
         "irrelevant"
         (const "non-linear")

  show (MaybeMisspelling err ns)
     = show err ++ "\nDid you mean" ++ case ns of
         (n ::: []) => ": " ++ n ++ "?"
         _ => " any of: " ++ showSep ", " (map show (forget ns)) ++ "?"
  show (ModuleNotFound fc ns)
      = show fc ++ ":" ++ show ns ++ " not found"
  show (GenericMsg fc str) = show fc ++ ":" ++ str
  show (UserError str) = "Error: " ++ str

  show (LexFail fc err) = show fc ++ ":Lexer error (" ++ show err ++ ")"
  show (ParseFail errs) = "Parse errors (" ++ show errs ++ ")"
  show (InternalError str) = "INTERNAL ERROR: " ++ str

  show (TTCErr err) = "TTC error: " ++ show err
  show (FileErr err) = "File error: " ++ show err

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
