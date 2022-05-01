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
     RApp : FC -> RawI -> RawC -> RawI
     RLet : FC -> RigCount -> Name -> (val : RawC) -> (ty : RawC) -> (scope : RawI) -> RawI
     RPi : FC -> RigCount -> Name -> (argty : RawC) -> (retty : RawC) -> RawI
     RPrimVal : FC -> Constant -> RawI
     RType : FC -> RawI

public export
data RawC : Type where
     RInf : FC -> RawI -> RawC -- inferrable, so must be checkable
     RLam : FC -> Name -> (scope : RawC) -> RawC
     RCase : FC -> (sc : RawI) -> List RawCaseAlt -> RawC

public export
data RawCaseAlt : Type where
     RConCase : Name -> List Name -> RawC -> RawCaseAlt
     RConstCase : Constant -> RawC -> RawCaseAlt
     RDefaultCase : RawC -> RawCaseAlt

public export
data RawCon : Type where
     RConDecl : Name -> RawC -> RawCon

public export
data RawData : Type where
     RDataDecl : Name -> RawC -> List RawCon -> RawData

public export
data RawDecl : Type where
     RData   : FC -> RawData -> RawDecl
     RTyDecl : FC -> Name -> RawC -> RawDecl
     RDef    : FC -> Name -> RawC -> RawDecl

-- Top level commands at the TT shell
public export
data Command : Type where
     Decl : RawDecl -> Command
     Eval : RawI -> Command

mutual -- grr
  -- I just threw these together. It'd be nice if the results paid
  -- attention to bracketing, being parsable, etc.
  export
  Show RawI where
    show (RAnnot fc tm ty)
        = assert_total $ "(" ++ show tm ++ " : " ++ show ty ++ ")"
    show (RVar fc n) = show n
    show (RApp fc f a)
        = assert_total $ "(" ++ show f ++ " " ++ show a ++ ")"
    show (RLet fc c n ty val sc)
        = assert_total $ "let " ++ show n ++ " : " ++ show ty ++
                         " = " ++ show val ++ " in "
                         ++ show sc
    show (RPi fc c n argty retty)
        = assert_total $ "pi " ++ show n ++ " : " ++ show argty ++ " . "
                         ++ show retty
    show (RPrimVal fc c) = show c
    show (RType fc) = "Type"

  export
  Show RawC where
    show (RInf fc t) = show t
    show (RLam fc n sc)
        = assert_total $ "lam " ++ show n ++ " . " ++ show sc
    show (RCase fc sc alts)
        = assert_total $
          "(case " ++ show sc ++ " of " ++
              showSep " | " (map show alts) ++ ")"

  export
  Show RawCaseAlt where
    show (RConCase n args sc)
        = assert_total $
          show n ++ " "
              ++ showSep " " (map show args) ++ " => "
              ++ show sc
    show (RConstCase c sc)
        = show c ++ " => " ++ show sc
    show (RDefaultCase sc)
        = "_ => " ++ show sc

export
Show RawCon where
  show (RConDecl n d) = show n ++ " : " ++ show d

export
Show RawData where
  show (RDataDecl n ty cons)
      = "data " ++ show n ++ " : " ++ show ty ++ " where { "
            ++ showSep " | " (map show cons) ++ " }"

export
Show RawDecl where
  show (RData _ d) = show d
  show (RTyDecl _ n d) = show n ++ " : " ++ show d ++ ";"
  show (RDef _ n d) = show n ++ " = " ++ show d ++ ";"

export
Show Command where
  show (Decl d) = "Decl " ++ show d
  show (Eval e) = "Eval " ++ show e
