module Core.Error

import Core.Binary
import public Core.Core

-- All the core TTImp errors

public export
data Error : Type where
     TTCErr : TTCError -> Error

public export
Core : Type -> Type
Core = CoreE Error

export
ttc : CoreTTC a -> Core a
ttc = wrap TTCErr
