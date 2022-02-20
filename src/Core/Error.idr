module Core.Error

import Core.Binary
import public Core.Core
import Core.TT

import Data.List1

-- All the core TTImp errors

public export
data Error : Type where
     UndefinedName : FC -> Name -> Error
     MaybeMisspelling : Error -> List1 String -> Error
     TTCErr : TTCError -> Error

public export
Core : Type -> Type
Core = CoreE Error

export
ttc : CoreTTC a -> Core a
ttc = wrap TTCErr
