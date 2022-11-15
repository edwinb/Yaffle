module Core.Syntax.Raw

import Core.Options.Log
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
     RCase : FC -> RigCount -> (sc : RawI) -> List RawCaseAlt -> RawC
     RMeta : FC -> String -> RawC
     RImplicit : FC -> RawC

public export
data RawCaseAlt : Type where
     RConCase : FC -> Name -> List Name -> RawC -> RawCaseAlt
     RConstCase : FC -> Constant -> RawC -> RawCaseAlt
     RDefaultCase : FC -> RawC -> RawCaseAlt

public export
data RawCon : Type where
     RConDecl : Name -> RawC -> RawCon

public export
data RawData : Type where
     RDataDecl : Name -> RawC -> List RawCon -> RawData

public export
data RawClause : Type where
     RClause : FC -> List (RigCount, Name, RawC) -> -- pattern variables
               RawI -> -- LHS
               RawC -> -- RHS
               RawClause

public export
data RawDecl : Type where
     RData   : FC -> RawData -> RawDecl
     RTyDecl : FC -> RigCount -> Name -> RawC -> RawDecl
     RDef    : FC -> Name -> RawC -> RawDecl
     RPatt   : FC -> Name -> List RawClause -> RawDecl

-- Top level commands at the TT shell
public export
data Command : Type where
     Decl : RawDecl -> Command
     Eval : RawI -> Command
     HNF : RawI -> Command
     Check : RawI -> Command
     Unify : RawI -> RawI -> Command
     Logging : LogLevel -> Command
     SizeChange : Name -> Command
     AutoSearch : RawC -> Command
     Quit : Command

prefixRig : RigCount -> String
prefixRig Rig0 = "0 "
prefixRig Rig1 = "1 "
prefixRig RigW = ""

prefixRig01 : RigCount -> String
prefixRig01 Rig0 = "0 "
prefixRig01 Rig1 = ""
prefixRig01 RigW = ""

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
        = assert_total $ "let " ++ prefixRig c ++ show n ++ " : " ++ show ty ++
                         " = " ++ show val ++ " in "
                         ++ show sc
    show (RPi fc c n argty retty)
        = assert_total $ "pi " ++ prefixRig c ++ show n ++ " : " ++ show argty ++ " . "
                         ++ show retty
    show (RPrimVal fc c) = show c
    show (RType fc) = "Type"

  export
  Show RawC where
    show (RInf fc t) = show t
    show (RLam fc n sc)
        = assert_total $ "lam " ++ show n ++ " . " ++ show sc
    show (RCase fc _ sc alts)
        = assert_total $
          "(case " ++ show sc ++ " of " ++
              showSep " | " (map show alts) ++ ")"
    show (RMeta fc str) = "?" ++ str
    show (RImplicit fc) = "_"

  export
  Show RawCaseAlt where
    show (RConCase fc n args sc)
        = assert_total $
          show n ++ " "
              ++ showSep " " (map show args) ++ " => "
              ++ show sc
    show (RConstCase fc c sc)
        = show c ++ " => " ++ show sc
    show (RDefaultCase fc sc)
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
Show RawClause where
  show (RClause _ ns lhs rhs)
      = show ns ++ " " ++ show lhs ++ " = " ++ show rhs

export
Show RawDecl where
  show (RData _ d) = show d
  show (RTyDecl _ c n d) = prefixRig01 c ++ show n ++ " : " ++ show d ++ ";"
  show (RDef _ n d) = show n ++ " = " ++ show d ++ ";"
  show (RPatt _ n cs) = show n ++ " { " ++ showSep "\n" (map show cs) ++ " }"

export
Show Command where
  show (Decl d) = "Decl " ++ show d
  show (Eval e) = "Eval " ++ show e
  show (HNF e) = "hnf " ++ show e
  show (Check e) = "type " ++ show e
  show (Unify x y) = "unify " ++ show x ++ " " ++ show y
  show (Logging i) = "logging " ++ show i
  show (SizeChange n) = "sc " ++ show n
  show (AutoSearch n) = "search " ++ show n
  show Quit = "quit"
