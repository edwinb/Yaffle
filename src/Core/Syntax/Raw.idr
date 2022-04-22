module Core.Syntax.Raw

import Core.TT

-- Raw terms, for typechecking the core

public export data RawI : Type -- inferrable
public export data RawC : Type -- checkable
public export data RawCaseAlt : Type

public export
data RawI : Type where
     RAnnot : FC -> RawC -> RawI -> RawI -- checkable with type annotation
     RVar : FC -> Name -> RawI
     RLam : FC -> Name -> (scope : RawI) -> RawI
     RLet : FC -> Name -> (val : RawI) -> (scope : RawI) -> RawI
     RPi : FC -> Name -> (argty : RawI) -> (retty : RawI) -> RawI
     RPrimVal : FC -> Constant -> RawI
     RType : FC -> RawI

public export
data RawC : Type where
     RInf : FC -> RawI -> RawC -- inferrable, so must be checkable
     RApp : FC -> RawI -> RawC -> RawC
     RCase : FC -> (sc : RawI) -> List RawCaseAlt -> RawC

public export
data RawCaseAlt : Type where
     RConCase : Name -> List Name -> RawC -> RawCaseAlt
     RConstCase : Constant -> RawC -> RawCaseAlt
     RDefaultCase : RawC -> RawCaseAlt

public export
data RawCon : Type where
     RConDecl : Name -> RawI -> RawCon

public export
data RawData : Type where
     RDataDecl : Name -> RawI -> List RawCon -> RawData

public export
data RawDecl : Type where
     RData   : RawData -> RawDecl
     RTyDecl : Name -> RawI -> RawDecl
     RDef    : Name -> RawI -> RawDecl

mutual -- grr
  export
  Show RawI where
    show (RAnnot fc tm ty)
        = assert_total $ "(" ++ show tm ++ " : " ++ show ty ++ ")"
    show (RVar fc n) = show n
    show (RLam fc n sc)
        = assert_total $ "(lam " ++ show n ++ " " ++ show sc ++ ")"
    show (RLet fc n val sc)
        = assert_total $ "(let (" ++ show n ++ " " ++ show val ++ ")"
                         ++ show sc ++ ")"
    show (RPi fc n argty retty)
        = assert_total $ "(pi (" ++ show n ++ " " ++ show argty ++ ")"
                         ++ show retty ++ ")"
    show (RPrimVal fc c) = show c
    show (RType fc) = "Type"

  export
  Show RawC where
    show (RInf fc t) = show t
    show (RApp fc f a) = "(" ++ show f ++ " " ++ show a ++ ")"
    show (RCase fc sc alts)
        = assert_total $
          "(case " ++ show sc ++ " " ++
              "[" ++ showSep " " (map show alts) ++ "])"

  export
  Show RawCaseAlt where
    show (RConCase n args sc)
        = assert_total $
          "((" ++ show n ++ " "
              ++ showSep " " (map show args) ++ ") "
              ++ show sc ++ ")"
    show (RConstCase c sc)
        = "(" ++ show c ++ " "
              ++ show sc ++ ")"
    show (RDefaultCase sc)
        = "(_ " ++ show sc ++ ")"
