module Core.Error

import Core.Binary
import public Core.Core
import Core.TT

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
     MaybeMisspelling : Error -> List1 String -> Error
     ModuleNotFound : FC -> ModuleIdent -> Error
     UserError : String -> Error
     LexFail : FC -> String -> Error
     ParseFail : List1 (FC, String) -> Error
     InternalError : String -> Error
     TTCErr : TTCError -> Error
     FileErr : TFileError -> Error

export
Show Error where
  show (ParseFail _) = "PARSE FAIL"
  show _ = ?todo

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
