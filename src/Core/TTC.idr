module Core.TTC

import Core.Binary.Prims
import Core.CompileExpr
import Core.Case.Patterns
import Core.Context
import Core.Core
import Core.Env
import Core.FC
import Core.Options
import Core.TT

import Libraries.Data.IntMap
import Libraries.Data.IOArray
import Libraries.Data.NameMap

import Data.Vect

%default covering

export
TTC Namespace where
  toBuf = toBuf . unsafeUnfoldNamespace
  fromBuf = do n <- fromBuf
               pure (unsafeFoldNamespace n)

export
TTC RawNamespace where
  toBuf (MkRawNS ns)
      = do let ns = unsafeUnfoldNamespace ns
           toBuf {a=Int} (cast (length ns))
           traverse_ (toBuf @{RawString}) ns
  fromBuf
      = do len <- fromBuf {a = Int}
           ns <- readElems [] (integerToNat (cast len))
           pure (MkRawNS (unsafeFoldNamespace ns))
    where
      readElems : List String -> Nat -> CoreTTC (List String)
      readElems xs Z = pure (reverse xs)
      readElems xs (S k)
          = do val <- fromBuf @{RawString}
               readElems (val :: xs) k

export
TTC ModuleIdent where
  toBuf = toBuf . unsafeUnfoldModuleIdent
  fromBuf = do n <- fromBuf
               pure (unsafeFoldModuleIdent n)

export
TTC VirtualIdent where
  toBuf Interactive = tag 0
  fromBuf =
    case !getTag of
      0 => pure Interactive
      _ => corrupt "VirtualIdent"

export
TTC OriginDesc where
  toBuf (PhysicalIdrSrc ident) = do tag 0; toBuf ident
  toBuf (PhysicalPkgSrc fname) = do tag 1; toBuf fname
  toBuf (Virtual ident) = do tag 2; toBuf ident

  fromBuf =
    case !getTag of
      0 => [| PhysicalIdrSrc fromBuf |]
      1 => [| PhysicalPkgSrc fromBuf |]
      2 => [| Virtual        fromBuf |]
      _ => corrupt "OriginDesc"

export
TTC FC where
  toBuf (MkFC file startPos endPos)
      = do tag 0; toBuf file; toBuf startPos; toBuf endPos
  toBuf (MkVirtualFC file startPos endPos)
      = do tag 2; toBuf file; toBuf startPos; toBuf endPos
  toBuf EmptyFC = tag 1

  fromBuf
      = case !getTag of
             0 => do f <- fromBuf;
                     s <- fromBuf; e <- fromBuf
                     pure (MkFC f s e)
             1 => pure EmptyFC
             2 => do f <- fromBuf;
                     s <- fromBuf; e <- fromBuf
                     pure (MkVirtualFC f s e)
             _ => corrupt "FC"

export
TTC Name where
  -- for efficiency reasons we do not encode UserName separately
  -- hence the nested pattern matches on UN (Basic/Hole/Field)
  toBuf (NS xs x) = do tag 0; toBuf xs; toBuf x
  toBuf (UN (Basic x)) = do tag 1; toBuf x
  toBuf (MN x y) = do tag 2; toBuf x; toBuf y
  toBuf (PV x y) = do tag 3; toBuf x; toBuf y
  toBuf (DN x y) = do tag 4; toBuf x; toBuf y
  toBuf (UN (Field x)) = do tag 5; toBuf x
  toBuf (Nested x y) = do tag 6; toBuf x; toBuf y
  toBuf (CaseBlock x y) = do tag 7; toBuf x; toBuf y
  toBuf (WithBlock x y) = do tag 8; toBuf x; toBuf y
  toBuf (Resolved x)
      = throw (Corrupt ("Can't write resolved name " ++ show x))
  toBuf (UN Underscore) = tag 9

  fromBuf
      = case !getTag of
             0 => do xs <- fromBuf
                     x <- fromBuf
                     pure (NS xs x)
             1 => do x <- fromBuf
                     pure (UN $ Basic x)
             2 => do x <- fromBuf
                     y <- fromBuf
                     pure (MN x y)
             3 => do x <- fromBuf
                     y <- fromBuf
                     pure (PV x y)
             4 => do x <- fromBuf
                     y <- fromBuf
                     pure (DN x y)
             5 => do x <- fromBuf
                     pure (UN $ Field x)
             6 => do x <- fromBuf
                     y <- fromBuf
                     pure (Nested x y)
             7 => do x <- fromBuf
                     y <- fromBuf
                     pure (CaseBlock x y)
             8 => do x <- fromBuf
                     y <- fromBuf
                     pure (WithBlock x y)
             9 => pure (UN Underscore)
             _ => corrupt "Name"

export
TTC RigCount where
  toBuf = elimSemi
              (tag 0)
              (tag 1)
              (const $ tag 2)

  fromBuf
      = case !getTag of
             0 => pure erased
             1 => pure linear
             2 => pure top
             _ => corrupt "RigCount"

export
TTC t => TTC (PiInfo t) where
  toBuf Implicit = tag 0
  toBuf Explicit = tag 1
  toBuf AutoImplicit = tag 2
  toBuf (DefImplicit r) = do tag 3; toBuf r

  fromBuf
      = case !getTag of
             0 => pure Implicit
             1 => pure Explicit
             2 => pure AutoImplicit
             3 => do t <- fromBuf; pure (DefImplicit t)
             _ => corrupt "PiInfo"

export
TTC PrimType where
  toBuf IntType     = tag 0
  toBuf Int8Type    = tag 1
  toBuf Int16Type   = tag 2
  toBuf Int32Type   = tag 3
  toBuf Int64Type   = tag 4
  toBuf IntegerType = tag 5
  toBuf Bits8Type   = tag 6
  toBuf Bits16Type  = tag 7
  toBuf Bits32Type  = tag 8
  toBuf Bits64Type  = tag 9
  toBuf StringType  = tag 10
  toBuf CharType    = tag 11
  toBuf DoubleType  = tag 12
  toBuf WorldType   = tag 13

  fromBuf = case !getTag of
    0  => pure IntType
    1  => pure Int8Type
    2  => pure Int16Type
    3  => pure Int32Type
    4  => pure Int64Type
    5  => pure IntegerType
    6  => pure Bits8Type
    7  => pure Bits16Type
    8  => pure Bits32Type
    9  => pure Bits64Type
    10 => pure StringType
    11 => pure CharType
    12 => pure DoubleType
    13 => pure WorldType
    _  => corrupt "PrimType"

export
TTC Constant where
  toBuf (I x)    = do tag 0;  toBuf x
  toBuf (I8 x)   = do tag 1;  toBuf x
  toBuf (I16 x)  = do tag 2;  toBuf x
  toBuf (I32 x)  = do tag 3;  toBuf x
  toBuf (I64 x)  = do tag 4;  toBuf x
  toBuf (BI x)   = do tag 5;  toBuf x
  toBuf (B8 x)   = do tag 6;  toBuf x
  toBuf (B16 x)  = do tag 7;  toBuf x
  toBuf (B32 x)  = do tag 8;  toBuf x
  toBuf (B64 x)  = do tag 9;  toBuf x
  toBuf (Str x)  = do tag 10; toBuf x
  toBuf (Ch x)   = do tag 11; toBuf x
  toBuf (Db x)   = do tag 12; toBuf x
  toBuf (PrT x)  = do tag 13; toBuf x
  toBuf WorldVal = tag 14

  fromBuf
      = case !getTag of
             0  => do x <- fromBuf; pure (I x)
             1  => do x <- fromBuf; pure (I8 x)
             2  => do x <- fromBuf; pure (I16 x)
             3  => do x <- fromBuf; pure (I32 x)
             4  => do x <- fromBuf; pure (I64 x)
             5  => do x <- fromBuf; pure (BI x)
             6  => do x <- fromBuf; pure (B8 x)
             7  => do x <- fromBuf; pure (B16 x)
             8  => do x <- fromBuf; pure (B32 x)
             9  => do x <- fromBuf; pure (B64 x)
             10 => do x <- fromBuf; pure (Str x)
             11 => do x <- fromBuf; pure (Ch x)
             12 => do x <- fromBuf; pure (Db x)
             13 => do x <- fromBuf; pure (PrT x)
             14 => pure WorldVal
             _ => corrupt "Constant"

export
TTC LazyReason where
  toBuf LInf = tag 0
  toBuf LLazy = tag 1
  toBuf LUnknown = tag 2

  fromBuf
      = case !getTag of
             0 => pure LInf
             1 => pure LLazy
             2 => pure LUnknown
             _ => corrupt "LazyReason"

export
TTC NameType where
  toBuf Bound = tag 0
  toBuf Func = tag 1
  toBuf (DataCon t arity) = do tag 2; toBuf t; toBuf arity
  toBuf (TyCon arity) = do tag 3; toBuf arity

  fromBuf
      = case !getTag of
             0 => pure Bound
             1 => pure Func
             2 => do x <- fromBuf; y <- fromBuf; pure (DataCon x y)
             3 => do x <- fromBuf; pure (TyCon x)
             _ => corrupt "NameType"

-- Assumption is that it was type safe when we wrote it out, so believe_me
-- to rebuild proofs is fine.
-- We're just making up the implicit arguments - this is only fine at run
-- time because those arguments get erased!
-- (Indeed, we're expecting the whole IsVar proof to be erased because
-- we have the idx...)
mkPrf : (idx : Nat) -> IsVar n idx ns
mkPrf {n} {ns} Z = believe_me (First {n} {ns = ns :< n})
mkPrf {n} {ns} (S k) = believe_me (Later {m=n} (mkPrf {n} {ns} k))

getName : (idx : Nat) -> SnocList Name -> Maybe Name
getName Z (xs :< x) = Just x
getName (S k) (xs :< x) = getName k xs
getName _ [<] = Nothing

export
{n : _} -> TTC (PrimFn n) where
  toBuf (Add ty) = do tag 0; toBuf ty
  toBuf (Sub ty) = do tag 1; toBuf ty
  toBuf (Mul ty) = do tag 2; toBuf ty
  toBuf (Div ty) = do tag 3; toBuf ty
  toBuf (Mod ty) = do tag 4; toBuf ty
  toBuf (Neg ty) = do tag 5; toBuf ty
  toBuf (ShiftL ty) = do tag 35; toBuf ty
  toBuf (ShiftR ty) = do tag 36; toBuf ty
  toBuf (BAnd ty) = do tag 37; toBuf ty
  toBuf (BOr ty) = do tag 38; toBuf ty
  toBuf (BXOr ty) = do tag 39; toBuf ty
  toBuf (LT ty) = do tag 6; toBuf ty
  toBuf (LTE ty) = do tag 7; toBuf ty
  toBuf (EQ ty) = do tag 8; toBuf ty
  toBuf (GTE ty) = do tag 9; toBuf ty
  toBuf (GT ty) = do tag 10; toBuf ty
  toBuf StrLength = tag 11
  toBuf StrHead = tag 12
  toBuf StrTail = tag 13
  toBuf StrIndex = tag 14
  toBuf StrCons = tag 15
  toBuf StrAppend = tag 16
  toBuf StrReverse = tag 17
  toBuf StrSubstr = tag 18

  toBuf DoubleExp = tag 19
  toBuf DoubleLog = tag 20
  toBuf DoublePow = tag 21
  toBuf DoubleSin = tag 22
  toBuf DoubleCos = tag 23
  toBuf DoubleTan = tag 24
  toBuf DoubleASin = tag 25
  toBuf DoubleACos = tag 26
  toBuf DoubleATan = tag 27
  toBuf DoubleSqrt = tag 32
  toBuf DoubleFloor = tag 33
  toBuf DoubleCeiling = tag 34

  toBuf (Cast x y) = do tag 99; toBuf x; toBuf y
  toBuf BelieveMe = tag 100
  toBuf Crash = tag 101

  fromBuf {n}
      = case n of
             S Z => fromBuf1
             S (S Z) => fromBuf2
             S (S (S Z)) => fromBuf3
             _ => corrupt "PrimFn"
    where
      fromBuf1 : CoreTTC (PrimFn 1)
      fromBuf1
          = case !getTag of
                 5 => do ty <- fromBuf; pure (Neg ty)
                 11 => pure StrLength
                 12 => pure StrHead
                 13 => pure StrTail
                 17 => pure StrReverse
                 19 => pure DoubleExp
                 20 => pure DoubleLog
                 22 => pure DoubleSin
                 23 => pure DoubleCos
                 24 => pure DoubleTan
                 25 => pure DoubleASin
                 26 => pure DoubleACos
                 27 => pure DoubleATan
                 32 => pure DoubleSqrt
                 33 => pure DoubleFloor
                 34 => pure DoubleCeiling

                 99 => do x <- fromBuf; y <- fromBuf; pure (Cast x y)
                 _ => corrupt "PrimFn 1"

      fromBuf2 : CoreTTC (PrimFn 2)
      fromBuf2
          = case !getTag of
                 0 => do ty <- fromBuf; pure (Add ty)
                 1 => do ty <- fromBuf; pure (Sub ty)
                 2 => do ty <- fromBuf; pure (Mul ty)
                 3 => do ty <- fromBuf; pure (Div ty)
                 4 => do ty <- fromBuf; pure (Mod ty)
                 6 => do ty <- fromBuf; pure (LT ty)
                 7 => do ty <- fromBuf; pure (LTE ty)
                 8 => do ty <- fromBuf; pure (EQ ty)
                 9 => do ty <- fromBuf; pure (GTE ty)
                 10 => do ty <- fromBuf; pure (GT ty)
                 14 => pure StrIndex
                 15 => pure StrCons
                 16 => pure StrAppend
                 21 => pure DoublePow
                 35 => do ty <- fromBuf; pure (ShiftL ty)
                 36 => do ty <- fromBuf; pure (ShiftR ty)
                 37 => do ty <- fromBuf; pure (BAnd ty)
                 38 => do ty <- fromBuf; pure (BOr ty)
                 39 => do ty <- fromBuf; pure (BXOr ty)
                 101 => pure Crash
                 _ => corrupt "PrimFn 2"

      fromBuf3 : CoreTTC (PrimFn 3)
      fromBuf3
          = case !getTag of
                 18 => pure StrSubstr
                 100 => pure BelieveMe
                 _ => corrupt "PrimFn 3"

mutual
  export
  {vars : _} -> TTC (Binder (Term vars)) where
    toBuf (Lam _ c x ty) = do tag 0; toBuf c; toBuf x; toBuf ty
    toBuf (Let _ c val ty) = do tag 1; toBuf c; toBuf val -- ; toBuf ty
    toBuf (Pi _ c x ty) = do tag 2; toBuf c; toBuf x; toBuf ty
    toBuf (PVar _ c p ty) = do tag 3; toBuf c; toBuf p; toBuf ty
    toBuf (PLet _ c val ty) = do tag 4; toBuf c; toBuf val -- ; toBuf ty
    toBuf (PVTy _ c ty) = do tag 5; toBuf c -- ; toBuf ty

    fromBuf
        = case !getTag of
               0 => do c <- fromBuf; x <- fromBuf; ty <- fromBuf; pure (Lam emptyFC c x ty)
               1 => do c <- fromBuf; x <- fromBuf; pure (Let emptyFC c x (Erased emptyFC Placeholder))
               2 => do c <- fromBuf; x <- fromBuf; y <- fromBuf; pure (Pi emptyFC c x y)
               3 => do c <- fromBuf; p <- fromBuf; ty <- fromBuf; pure (PVar emptyFC c p ty)
               4 => do c <- fromBuf; x <- fromBuf; pure (PLet emptyFC c x (Erased emptyFC Placeholder))
               5 => do c <- fromBuf; pure (PVTy emptyFC c (Erased emptyFC Placeholder))
               _ => corrupt "Binder"

  export
  TTC UseSide where
    toBuf UseLeft = tag 0
    toBuf UseRight = tag 1

    fromBuf
        = case !getTag of
               0 => pure UseLeft
               1 => pure UseRight
               _ => corrupt "UseSide"

  export
  TTC CaseType where
    toBuf PatMatch = tag 0
    toBuf (CaseBlock n) = do tag 1; toBuf n

    fromBuf
        = case !getTag of
               0 => pure PatMatch
               1 => do n <- fromBuf; pure (CaseBlock n)
               _ => corrupt "CaseType"


  export
  {vars : _} -> TTC (Term vars) where
    toBuf (Local {name} fc idx y)
        = if idx < 241
             then do tag (15 + cast idx)
             else do tag 0
                     toBuf idx
    toBuf (Ref fc nt name)
        = do tag 1;
             toBuf nt; toBuf name
    toBuf (Meta fc n i xs)
        = do tag 2;
             toBuf n; toBuf xs
    toBuf (Bind fc x bnd scope)
        = do tag 3;
             toBuf x;
             toBuf bnd; toBuf scope
    toBuf (App fc fn c arg)
        = do tag 4
             toBuf fn
             toBuf c
             toBuf arg
    toBuf (As fc s as tm)
        = do tag 5;
             toBuf s; toBuf as; toBuf tm
    toBuf (Case fc t c sc scty alts)
        = do tag 6
             toBuf t; toBuf c; toBuf sc; toBuf scty
             toBuf alts
    toBuf (TDelayed fc r tm)
        = do tag 7;
             toBuf r; toBuf tm
    toBuf (TDelay fc r ty tm)
        = do tag 8;
             toBuf r; toBuf ty; toBuf tm
    toBuf (TForce fc r tm)
        = do tag 9;
             toBuf r; toBuf tm
    toBuf (PrimVal fc c)
        = do tag 10;
             toBuf c
    toBuf (PrimOp {arity} fc fn args)
        = do tag 11
             toBuf arity
             toBuf fn
             toBuf args
    toBuf (Erased fc _)
        = tag 12
    toBuf (Unmatched fc str)
        = do tag 13
             toBuf str
    toBuf (TType fc u)
        = do tag 14; toBuf u

    fromBuf {vars}
        = case !getTag of
               0 => do idx <- fromBuf
                       name <- maybe (corrupt "Term") pure
                                     (getName idx vars)
                       pure (Local {name} emptyFC idx (mkPrf idx))
               1 => do nt <- fromBuf; name <- fromBuf
                       pure (Ref emptyFC nt name)
               2 => do n <- fromBuf
                       xs <- fromBuf
                       pure (Meta emptyFC n 0 xs) -- needs resolving
               3 => do x <- fromBuf
                       bnd <- fromBuf; scope <- fromBuf
                       pure (Bind emptyFC x bnd scope)
               4 => do fn <- fromBuf
                       c <- fromBuf
                       arg <- fromBuf
                       pure (App emptyFC fn c arg)
               5 => do s <- fromBuf; as <- fromBuf; tm <- fromBuf
                       pure (As emptyFC s as tm)
               6 => do t <- fromBuf; c <- fromBuf; sc <- fromBuf; scty <- fromBuf
                       alts <- fromBuf
                       pure (Case emptyFC t c sc scty alts)
               7 => do lr <- fromBuf; tm <- fromBuf
                       pure (TDelayed emptyFC lr tm)
               8 => do lr <- fromBuf;
                       ty <- fromBuf; tm <- fromBuf
                       pure (TDelay emptyFC lr ty tm)
               9 => do lr <- fromBuf; tm <- fromBuf
                       pure (TForce emptyFC lr tm)
               10 => do c <- fromBuf
                        pure (PrimVal emptyFC c)
               11 => do arity <- fromBuf
                        op <- fromBuf
                        args <- fromBuf
                        pure (PrimOp {arity} emptyFC op args)
               12 => pure (Erased emptyFC Placeholder)
               13 => do str <- fromBuf
                        pure (Unmatched emptyFC str)
               14 => do u <- fromBuf; pure (TType emptyFC u)
               idxp => do let idx : Nat = fromInteger (cast (idxp - 15))
                          let Just name = getName idx vars
                              | Nothing => corrupt "Term"
                          pure (Local {name} emptyFC idx (mkPrf idx))

  export
  {vars : _} -> TTC (CaseScope vars) where
    toBuf (RHS _ tm) = do tag 0; toBuf tm
    toBuf (Arg c x sc) = do tag 1; toBuf c; toBuf x; toBuf sc

    fromBuf
        = case !getTag of
               0 => do tm <- fromBuf
                       pure (RHS [] tm)
               1 => do c <- fromBuf; x <- fromBuf; sc <- fromBuf
                       pure (Arg c x sc)
               _ => corrupt "CaseScope"

  export
  {vars : _} -> TTC (CaseAlt vars) where
    toBuf (ConCase fc n t sc) = do tag 0; toBuf n; toBuf t; toBuf sc
    toBuf (DelayCase fc t a tm) = do tag 1; toBuf t; toBuf a; toBuf tm
    toBuf (ConstCase fc c tm) = do tag 2; toBuf c; toBuf tm
    toBuf (DefaultCase fc tm) = do tag 3; toBuf tm

    fromBuf
        = case !getTag of
               0 => do n <- fromBuf; t <- fromBuf; sc <- fromBuf
                       pure (ConCase emptyFC n t sc)
               1 => do t <- fromBuf; a <- fromBuf; tm <- fromBuf
                       pure (DelayCase emptyFC t a tm)
               2 => do c <- fromBuf; tm <- fromBuf
                       pure (ConstCase emptyFC c tm)
               3 => do tm <- fromBuf
                       pure (DefaultCase emptyFC tm)
               _ => corrupt "CaseScope"

export
TTC Pat where
  toBuf (PAs fc x y)
      = do tag 0; toBuf fc; toBuf x; toBuf y
  toBuf (PCon fc x t arity xs)
      = do tag 1; toBuf fc; toBuf x; toBuf t; toBuf arity; toBuf xs
  toBuf (PTyCon fc x arity xs)
      = do tag 2; toBuf fc; toBuf x; toBuf arity; toBuf xs
  toBuf (PConst fc c)
      = do tag 3; toBuf fc; toBuf c
  toBuf (PArrow fc x s t)
      = do tag 4; toBuf fc; toBuf x; toBuf s; toBuf t
  toBuf (PDelay fc x t y)
      = do tag 5; toBuf fc; toBuf x; toBuf t; toBuf y
  toBuf (PLoc fc x)
      = do tag 6; toBuf fc; toBuf x
  toBuf (PUnmatchable fc x)
      = do tag 7; toBuf fc; toBuf x

  fromBuf
      = case !getTag of
             0 => do fc <- fromBuf; x <- fromBuf;
                     y <- fromBuf
                     pure (PAs fc x y)
             1 => do fc <- fromBuf; x <- fromBuf
                     t <- fromBuf; arity <- fromBuf
                     xs <- fromBuf
                     pure (PCon fc x t arity xs)
             2 => do fc <- fromBuf; x <- fromBuf
                     arity <- fromBuf
                     xs <- fromBuf
                     pure (PTyCon fc x arity xs)
             3 => do fc <- fromBuf; c <- fromBuf
                     pure (PConst fc c)
             4 => do fc <- fromBuf; x <- fromBuf
                     s <- fromBuf; t <- fromBuf
                     pure (PArrow fc x s t)
             5 => do fc <- fromBuf; x <- fromBuf;
                     t <- fromBuf; y <- fromBuf
                     pure (PDelay fc x t y)
             6 => do fc <- fromBuf; x <- fromBuf
                     pure (PLoc fc x)
             7 => do fc <- fromBuf; x <- fromBuf
                     pure (PUnmatchable fc x)
             _ => corrupt "Pat"

export
{vars : _} -> TTC (Env Term vars) where
  toBuf [<] = pure ()
  toBuf (env :< bnd)
      = do toBuf env; toBuf bnd

  -- Length has to correspond to length of 'vars'
  fromBuf {vars = [<]} = pure [<]
  fromBuf {vars = xs :< x}
      = do env <- fromBuf
           bnd <- fromBuf
           pure (env :< bnd)

export
TTC Visibility where
  toBuf Private = tag 0
  toBuf Export = tag 1
  toBuf Public = tag 2

  fromBuf
      = case !getTag of
             0 => pure Private
             1 => pure Export
             2 => pure Public
             _ => corrupt "Visibility"

export
TTC PartialReason where
  toBuf NotStrictlyPositive = tag 0
  toBuf (BadCall xs) = do tag 1; toBuf xs
  toBuf (BadPath xs n) = do tag 2; toBuf xs; toBuf n
  toBuf (RecPath xs) = do tag 3; toBuf xs

  fromBuf
      = case !getTag of
             0 => pure NotStrictlyPositive
             1 => do xs <- fromBuf
                     pure (BadCall xs)
             2 => do xs <- fromBuf
                     n <- fromBuf
                     pure (BadPath xs n)
             3 => do xs <- fromBuf
                     pure (RecPath xs)
             _ => corrupt "PartialReason"

export
TTC Terminating where
  toBuf Unchecked = tag 0
  toBuf IsTerminating = tag 1
  toBuf (NotTerminating p) = do tag 2; toBuf p

  fromBuf
      = case !getTag of
             0 => pure Unchecked
             1 => pure IsTerminating
             2 => do p <- fromBuf
                     pure (NotTerminating p)
             _ => corrupt "Terminating"

export
TTC Covering where
  toBuf IsCovering = tag 0
  toBuf (MissingCases ms)
      = do tag 1
           toBuf ms
  toBuf (NonCoveringCall ns)
      = do tag 2
           toBuf ns

  fromBuf
      = case !getTag of
             0 => pure IsCovering
             1 => do ms <- fromBuf
                     pure (MissingCases ms)
             2 => do ns <- fromBuf
                     pure (NonCoveringCall ns)
             _ => corrupt "Covering"

export
TTC Totality where
  toBuf (MkTotality term cov) = do toBuf term; toBuf cov

  fromBuf
      = do term <- fromBuf
           cov <- fromBuf
           pure (MkTotality term cov)

export
TTC ConInfo where
  toBuf DATACON = tag 0
  toBuf TYCON = tag 1
  toBuf NIL = tag 2
  toBuf CONS = tag 3
  toBuf (ENUM n) = do tag 4; toBuf n
  toBuf NOTHING = tag 5
  toBuf JUST = tag 6
  toBuf RECORD = tag 7
  toBuf ZERO = tag 8
  toBuf SUCC = tag 9
  toBuf UNIT = tag 10

  fromBuf
      = case !getTag of
             0 => pure DATACON
             1 => pure TYCON
             2 => pure NIL
             3 => pure CONS
             4 => do n <- fromBuf; pure (ENUM n)
             5 => pure NOTHING
             6 => pure JUST
             7 => pure RECORD
             8 => pure ZERO
             9 => pure SUCC
             10 => pure UNIT
             _ => corrupt "ConInfo"

mutual
  export
  {vars : _} -> TTC (CExp vars) where
    toBuf (CLocal fc {x} {idx} h) = do tag 0; toBuf fc; toBuf idx
    toBuf (CRef fc n) = do tag 1; toBuf fc; toBuf n
    toBuf (CLam fc x sc) = do tag 2; toBuf fc; toBuf x; toBuf sc
    toBuf (CLet fc x inl val sc) = do tag 3; toBuf fc; toBuf x; toBuf inl; toBuf val; toBuf sc
    toBuf (CApp fc f as) = assert_total $ do tag 4; toBuf fc; toBuf f; toBuf as
    toBuf (CCon fc t n ci as) = assert_total $ do tag 5; toBuf fc; toBuf t; toBuf n; toBuf ci; toBuf as
    toBuf (COp {arity} fc op as) = assert_total $ do tag 6; toBuf fc; toBuf arity; toBuf op; toBuf as
    toBuf (CExtPrim fc f as) = assert_total $ do tag 7; toBuf fc; toBuf f; toBuf as
    toBuf (CForce fc lr x) = assert_total $ do tag 8; toBuf fc; toBuf lr; toBuf x
    toBuf (CDelay fc lr x) = assert_total $ do tag 9; toBuf fc; toBuf lr; toBuf x
    toBuf (CConCase fc sc alts def) = assert_total $ do tag 10; toBuf fc; toBuf sc; toBuf alts; toBuf def
    toBuf (CConstCase fc sc alts def) = assert_total $ do tag 11; toBuf fc; toBuf sc; toBuf alts; toBuf def
    toBuf (CPrimVal fc c) = do tag 12; toBuf fc; toBuf c
    toBuf (CErased fc) = do tag 13; toBuf fc
    toBuf (CCrash fc msg) = do tag 14; toBuf fc; toBuf msg

    fromBuf
        = assert_total $ case !getTag of
               0 => do fc <- fromBuf
                       idx <- fromBuf
                       let Just x = getName idx vars
                           | Nothing => corrupt "CExp"
                       pure (CLocal {x} fc (mkPrf idx))
               1 => do fc <- fromBuf
                       n <- fromBuf
                       pure (CRef fc n)
               2 => do fc <- fromBuf
                       x <- fromBuf; sc <- fromBuf
                       pure (CLam fc x sc)
               3 => do fc <- fromBuf
                       x <- fromBuf; inl <- fromBuf; val <- fromBuf; sc <- fromBuf
                       pure (CLet fc x inl val sc)
               4 => do fc <- fromBuf
                       f <- fromBuf; as <- fromBuf
                       pure (CApp fc f as)
               5 => do fc <- fromBuf
                       t <- fromBuf; n <- fromBuf; ci <- fromBuf; as <- fromBuf
                       pure (CCon fc t n ci as)
               6 => do fc <- fromBuf
                       arity <- fromBuf; op <- fromBuf; args <- fromBuf
                       pure (COp {arity} fc op args)
               7 => do fc <- fromBuf
                       p <- fromBuf; as <- fromBuf
                       pure (CExtPrim fc p as)
               8 => do fc <- fromBuf
                       lr <- fromBuf
                       x <- fromBuf
                       pure (CForce fc lr x)
               9 => do fc <- fromBuf
                       lr <- fromBuf
                       x <- fromBuf
                       pure (CDelay fc lr x)
               10 => do fc <- fromBuf
                        sc <- fromBuf; alts <- fromBuf; def <- fromBuf
                        pure (CConCase fc sc alts def)
               11 => do fc <- fromBuf
                        sc <- fromBuf; alts <- fromBuf; def <- fromBuf
                        pure (CConstCase fc sc alts def)
               12 => do fc <- fromBuf
                        c <- fromBuf
                        pure (CPrimVal fc c)
               13 => do fc <- fromBuf
                        pure (CErased fc)
               14 => do fc <- fromBuf
                        msg <- fromBuf
                        pure (CCrash fc msg)
               _ => corrupt "CExp"

  export
  {vars : _} -> TTC (CCaseScope vars) where
    toBuf (CRHS sc) = do tag 0; toBuf sc
    toBuf (CArg x sc) = do tag 1; toBuf x; toBuf sc

    fromBuf
        = case !getTag of
               0 => do sc <- fromBuf
                       pure (CRHS sc)
               1 => do x <- fromBuf; sc <- fromBuf
                       pure (CArg x sc)
               _ => corrupt "CCaseScope"

  export
  {vars : _} -> TTC (CConAlt vars) where
    toBuf (MkConAlt n ci t sc) = do toBuf n; toBuf ci; toBuf t; toBuf sc

    fromBuf
        = do n <- fromBuf; ci <- fromBuf; t <- fromBuf; sc <- fromBuf
             pure (MkConAlt n ci t sc)

  export
  {vars : _} -> TTC (CConstAlt vars) where
    toBuf (MkConstAlt c sc) = do toBuf c; toBuf sc

    fromBuf
        = do c <- fromBuf; sc <- fromBuf
             pure (MkConstAlt c sc)

export
TTC CFType where
  toBuf CFUnit = tag 0
  toBuf CFInt = tag 1
  toBuf CFUnsigned8 = tag 2
  toBuf CFUnsigned16 = tag 3
  toBuf CFUnsigned32 = tag 4
  toBuf CFUnsigned64 = tag 5
  toBuf CFString = tag 6
  toBuf CFDouble = tag 7
  toBuf CFChar = tag 8
  toBuf CFPtr = tag 9
  toBuf CFWorld = tag 10
  toBuf (CFFun s t) = do tag 11; toBuf s; toBuf t
  toBuf (CFIORes t) = do tag 12; toBuf t
  toBuf (CFStruct n a) = do tag 13; toBuf n; toBuf a
  toBuf (CFUser n a) = do tag 14; toBuf n; toBuf a
  toBuf CFGCPtr = tag 15
  toBuf CFBuffer = tag 16
  toBuf CFInt8 = tag 17
  toBuf CFInt16 = tag 18
  toBuf CFInt32 = tag 19
  toBuf CFInt64 = tag 20
  toBuf CFForeignObj = tag 21
  toBuf CFInteger = tag 22

  fromBuf
      = case !getTag of
             0 => pure CFUnit
             1 => pure CFInt
             2 => pure CFUnsigned8
             3 => pure CFUnsigned16
             4 => pure CFUnsigned32
             5 => pure CFUnsigned64
             6 => pure CFString
             7 => pure CFDouble
             8 => pure CFChar
             9 => pure CFPtr
             10 => pure CFWorld
             11 => do s <- fromBuf; t <- fromBuf; pure (CFFun s t)
             12 => do t <- fromBuf; pure (CFIORes t)
             13 => do n <- fromBuf; a <- fromBuf; pure (CFStruct n a)
             14 => do n <- fromBuf; a <- fromBuf; pure (CFUser n a)
             15 => pure CFGCPtr
             16 => pure CFBuffer
             17 => pure CFInt8
             18 => pure CFInt16
             19 => pure CFInt32
             20 => pure CFInt64
             21 => pure CFForeignObj
             22 => pure CFInteger
             _ => corrupt "CFType"

export
TTC CDef where
  toBuf (MkFun args cexpr) = do tag 0; toBuf args; toBuf cexpr
  toBuf (MkCon t arity pos) = do tag 1; toBuf t; toBuf arity; toBuf pos
  toBuf (MkForeign cs args ret) = do tag 2; toBuf cs; toBuf args; toBuf ret
  toBuf (MkError cexpr) = do tag 3; toBuf cexpr

  fromBuf
      = case !getTag of
             0 => do args <- fromBuf; cexpr <- fromBuf
                     pure (MkFun args cexpr)
             1 => do t <- fromBuf; arity <- fromBuf; pos <- fromBuf
                     pure (MkCon t arity pos)
             2 => do cs <- fromBuf; args <- fromBuf; ret <- fromBuf
                     pure (MkForeign cs args ret)
             3 => do cexpr <- fromBuf
                     pure (MkError cexpr)
             _ => corrupt "CDef"

export
TTC CG where
  toBuf Chez = tag 0
  toBuf ChezSep = tag 1
  toBuf Racket = tag 2
  toBuf (Other s) = do tag 4; toBuf s
  toBuf Node = tag 5
  toBuf Javascript = tag 6
  toBuf RefC = tag 7
  toBuf VMCodeInterp = tag 8

  fromBuf
      = case !getTag of
             0 => pure Chez
             1 => pure ChezSep
             2 => pure Racket
             4 => do s <- fromBuf
                     pure (Other s)
             5 => pure Node
             6 => pure Javascript
             7 => pure RefC
             8 => pure VMCodeInterp
             _ => corrupt "CG"

-- Incremental so needs to be done without string table
export
[IncData] TTC (List (CG, String, List String)) where
  toBuf xs
      = do toBuf (TailRec_length xs)
           traverse_ toBufEntry xs
    where
      length_aux : List a -> Int -> Int
      length_aux [] len = len
      length_aux (_::xs) len = length_aux xs (1 + len)

      TailRec_length : List a -> Int
      TailRec_length xs = length_aux xs 0

      toBufEntry : (CG, String, List String) -> CoreTTC ()
      toBufEntry (cg, f, fs)
          = do toBuf cg
               toBuf @{RawString} f
               toBuf (TailRec_length fs)
               traverse_ (toBuf @{RawString}) fs

  fromBuf
      = do len <- fromBuf {a = Int}
           readElems [] (integerToNat (cast len))
    where
      readRawStrings : Nat -> CoreTTC (List String)
      readRawStrings Z = pure []
      readRawStrings (S k)
          = do s <- fromBuf @{RawString}
               ss <- readRawStrings k
               pure (s :: ss)

      readElem : CoreTTC (CG, String, List String)
      readElem
          = do cg <- fromBuf
               f <- fromBuf @{RawString}
               len <- fromBuf {a = Int}
               fs <- readRawStrings (integerToNat (cast len))
               pure (cg, f, fs)

      readElems : List (CG, String, List String) -> Nat ->
                  CoreTTC (List (CG, String, List String))
      readElems xs Z = pure (reverse xs)
      readElems xs (S k)
          = do val <- readElem
               readElems (val :: xs) k

export
TTC PairNames where
  toBuf l
      = do toBuf (pairType l)
           toBuf (fstName l)
           toBuf (sndName l)
  fromBuf
      = do ty <- fromBuf
           d <- fromBuf
           f <- fromBuf
           pure (MkPairNs ty d f)

export
TTC RewriteNames where
  toBuf l
      = do toBuf (equalType l)
           toBuf (rewriteName l)
  fromBuf
      = do ty <- fromBuf
           l <- fromBuf
           pure (MkRewriteNs ty l)

export
TTC PrimNames where
  toBuf l
      = do toBuf (fromIntegerName l)
           toBuf (fromStringName l)
           toBuf (fromCharName l)
           toBuf (fromDoubleName l)
  fromBuf
      = do i <- fromBuf
           str <- fromBuf
           c <- fromBuf
           d <- fromBuf
           pure (MkPrimNs i str c d)

export
TTC TotalReq where
  toBuf Total = tag 0
  toBuf CoveringOnly = tag 1
  toBuf PartialOK = tag 2

  fromBuf
      = case !getTag of
             0 => pure Total
             1 => pure CoveringOnly
             2 => pure PartialOK
             _ => corrupt "TotalReq"

TTC DefFlag where
  toBuf Inline = tag 2
  toBuf NoInline = tag 14
  toBuf Deprecate = tag 15
  toBuf Invertible = tag 3
  toBuf Overloadable = tag 4
  toBuf TCInline = tag 5
  toBuf (SetTotal x) = do tag 6; toBuf x
  toBuf BlockedHint = tag 7
  toBuf BlockReduce = tag 8
  toBuf Macro = tag 9
  toBuf (PartialEval x) = tag 10 -- names not useful any more
  toBuf AllGuarded = tag 11
  toBuf (ConType ci) = do tag 12; toBuf ci
  toBuf (Identity x) = do tag 13; toBuf x

  fromBuf
      = case !getTag of
             2 => pure Inline
             3 => pure Invertible
             4 => pure Overloadable
             5 => pure TCInline
             6 => do x <- fromBuf; pure (SetTotal x)
             7 => pure BlockedHint
             8 => pure BlockReduce
             9 => pure Macro
             10 => pure (PartialEval [])
             11 => pure AllGuarded
             12 => do ci <- fromBuf; pure (ConType ci)
             13 => do x <- fromBuf; pure (Identity x)
             14 => pure NoInline
             15 => pure Deprecate
             _ => corrupt "DefFlag"

export
TTC SizeChange where
  toBuf Smaller = tag 0
  toBuf Same = tag 1
  toBuf Unknown = tag 2

  fromBuf
      = case !getTag of
             0 => pure Smaller
             1 => pure Same
             2 => pure Unknown
             _ => corrupt "SizeChange"

export
TTC SCCall where
  toBuf c = do toBuf (fnCall c); toBuf (fnArgs c); toBuf (fnLoc c)
  fromBuf
      = do fn <- fromBuf
           args <- fromBuf
           loc <- fromBuf
           pure (MkSCCall fn args loc)

export
TTC Transform where
  toBuf (MkTransform {vars} n env lhs rhs)
      = do toBuf vars
           toBuf n
           toBuf env
           toBuf lhs
           toBuf rhs

  fromBuf
      = do vars <- fromBuf
           n <- fromBuf
           env <- fromBuf
           lhs <- fromBuf
           rhs <- fromBuf
           pure (MkTransform {vars} n env lhs rhs)

export
TTC HoleInfo where
  toBuf NotHole = tag 0
  toBuf (SolvedHole n) = do tag 1; toBuf n

  fromBuf
      = case !getTag of
             0 => pure NotHole
             1 => do n <- fromBuf; pure (SolvedHole n)
             _ => corrupt "HoleInfo"

export
TTC FnInfo where
  toBuf l
      = do toBuf (holeInfo l)
           toBuf (alwaysReduce l)
           toBuf (externalDecl l)
  fromBuf
      = do h <- fromBuf
           r <- fromBuf
           e <- fromBuf
           pure (MkFnInfo h r e)

export
TTC TyConInfo where
  toBuf l
      = do toBuf (paramPos l)
           toBuf (deterArgs l)
           toBuf (mutWith l)
           toBuf (datacons l)
           toBuf (detagBy l)
           toBuf (uniqueAuto l)
           toBuf (external l)
  fromBuf
      = do p <- fromBuf; d <- fromBuf; m <- fromBuf
           c <- fromBuf; t <- fromBuf; u <- fromBuf
           e <- fromBuf
           pure (MkTyConInfo p d m c t u e)

export
TTC DataConInfo where
  toBuf l
      = do toBuf (quantities l)
           toBuf (newTypeArg l)
  fromBuf
      = do q <- fromBuf; n <- fromBuf
           pure (MkDataConInfo q n)

export
TTC Clause where
  toBuf (MkClause {vars} env lhs rhs)
      = do toBuf vars; toBuf env; toBuf lhs; toBuf rhs
  fromBuf
      = do vars <- fromBuf; env <- fromBuf; lhs <- fromBuf; rhs <- fromBuf
           pure (MkClause {vars} env lhs rhs)

export
TTC Def where
  toBuf None = tag 0
  toBuf (Function fi ct rt pats)
      = do tag 1; toBuf fi; toBuf ct; toBuf pats
  toBuf (DCon d t arity) = do tag 2; toBuf d; toBuf t; toBuf arity
  toBuf (TCon t arity)
      = do tag 3; toBuf t; toBuf arity
  toBuf (Hole locs p)
      = do tag 4; toBuf locs; toBuf (implbind p)
  toBuf (BySearch c depth def)
      = do tag 5; toBuf c; toBuf depth; toBuf def
  toBuf (Guess guess envb constraints)
      = do tag 6; toBuf guess; toBuf envb; toBuf constraints
  toBuf (ExternDef a)
      = do tag 7; toBuf a
  toBuf (ForeignDef a cs)
      = do tag 8; toBuf a; toBuf cs
  toBuf ImpBind = tag 9
  toBuf (UniverseLevel i) = do tag 10; toBuf i
  toBuf Delayed = tag 11

  fromBuf
      = case !getTag of
             0 => pure None
             1 => do fi <- fromBuf
                     ct <- fromBuf
                     pats <- fromBuf
                     pure (Function fi ct (Unmatched emptyFC "") pats)
             2 => do d <- fromBuf; t <- fromBuf; a <- fromBuf
                     pure (DCon d t a)
             3 => do t <- fromBuf; a <- fromBuf
                     pure (TCon t a)
             4 => do l <- fromBuf; p <- fromBuf
                     pure (Hole l (holeInit p))
             5 => do c <- fromBuf; depth <- fromBuf
                     def <- fromBuf
                     pure (BySearch c depth def)
             6 => do g <- fromBuf; envb <- fromBuf; cs <- fromBuf
                     pure (Guess g envb cs)
             7 => do a <- fromBuf
                     pure (ExternDef a)
             8 => do a <- fromBuf; cs <- fromBuf
                     pure (ForeignDef a cs)
             9 => pure ImpBind
             10 => do l <- fromBuf
                      pure (UniverseLevel l)
             11 => pure Delayed
             _ => corrupt "Def"

export
TTC GlobalDef where
  toBuf gdef
      = -- Only write full details for user specified names. The others will
        -- be holes where all we will ever need after loading is the definition
        do toBuf (compexpr gdef)
           toBuf (map NameMap.toList (refersToRuntimeM gdef))
           toBuf (location gdef)
           -- We don't need any of the rest for code generation, so if
           -- we're decoding then, we can skip these (see Compiler.Common
           -- for how it's decoded minimally there)
           toBuf (multiplicity gdef)
           toBuf (fullname gdef)
           toBuf (map NameMap.toList (refersToM gdef))
           toBuf (definition gdef)
           when (isUserName (fullname gdef) || cwName (fullname gdef)) $
              do toBuf (type gdef)
                 toBuf (eraseArgs gdef)
                 toBuf (safeErase gdef)
                 toBuf (specArgs gdef)
                 toBuf (inferrable gdef)
                 toBuf (localVars gdef)
                 toBuf (visibility gdef)
                 toBuf (totality gdef)
                 toBuf (flags gdef)
                 toBuf (invertible gdef)
                 toBuf (sizeChange gdef)
    where
      cwName : Name -> Bool
      cwName (CaseBlock _ _) = True
      cwName (WithBlock _ _) = True
      cwName _ = False
  fromBuf
      = do cdef <- fromBuf
           refsRList <- fromBuf
           let refsR = map fromList refsRList
           loc <- fromBuf
           mul <- fromBuf
           name <- fromBuf
           refsList <- fromBuf
           let refs = map fromList refsList
           def <- fromBuf
           if isUserName name
              then do ty <- fromBuf
                      eargs <- fromBuf
                      seargs <- fromBuf
                      specargs <- fromBuf
                      iargs <- fromBuf
                      vars <- fromBuf
                      vis <- fromBuf
                      tot <- fromBuf
                      fl <- fromBuf
                      inv <- fromBuf
                      sc <- fromBuf
                      pure (MkGlobalDef loc name ty eargs seargs specargs iargs
                                        mul vars vis
                                        tot fl refs refsR inv def cdef Nothing sc Nothing)
              else pure (MkGlobalDef loc name (Erased loc Placeholder) [] [] [] []
                                     mul [<] Public unchecked [] refs refsR
                                     False def cdef Nothing [] Nothing)

Core.Context.Ctxt.decode gam idx update (Coded bin)
    = do b <- newRef Bin bin
         def <- ttc $ fromBuf {a = GlobalDef}

         let a = getContent gam
         arr <- get Arr
         def' <- resolved gam def
         when update $ coreLift $ writeArray arr idx (Decoded def')
         pure def'
Core.Context.Ctxt.decode gam idx update (Decoded def) = pure def
