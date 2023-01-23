module Idris.Pretty.TT

import Core.TT
import Idris.Pretty.Annotations

import Data.String
import Data.Vect

import Libraries.Data.String.Extra
import public Libraries.Text.PrettyPrint.Prettyprinter

Pretty IdrisSyntax PrimType where
  pretty c = annotate (TCon Nothing) $ case c of
    IntType => "Int"
    Int8Type => "Int8"
    Int16Type => "Int16"
    Int32Type => "Int32"
    Int64Type => "Int64"
    IntegerType => "Integer"
    Bits8Type => "Bits8"
    Bits16Type => "Bits16"
    Bits32Type => "Bits32"
    Bits64Type => "Bits64"
    StringType => "String"
    CharType => "Char"
    DoubleType => "Double"
    WorldType => "%World"

export
Pretty IdrisSyntax Constant where
  pretty (PrT x) = pretty x
  pretty v = annotate (DCon Nothing) $ pretty0 $ show v

export
prettyOp : PrimFn arity -> Vect arity (Doc IdrisSyntax) -> Doc IdrisSyntax
prettyOp op@(Add ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "+" <++> v2
prettyOp op@(Sub ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "-" <++> v2
prettyOp op@(Mul ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "*" <++> v2
prettyOp op@(Div ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "`div`" <++> v2
prettyOp op@(Mod ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "`mod`" <++> v2
prettyOp op@(Neg ty) [v] = annotate (Fun $ UN $ Basic $ show op) "-" <++> v
prettyOp op@(ShiftL ty) [v1,v2] = annotate (Fun $ UN $ Basic $ show op) "shiftl" <++> v1 <++> v2
prettyOp op@(ShiftR ty) [v1,v2] = annotate (Fun $ UN $ Basic $ show op) "shiftr" <++> v1 <++> v2
prettyOp op@(BAnd ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "&&" <++> v2
prettyOp op@(BOr ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "||" <++> v2
prettyOp op@(BXOr ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "`xor`" <++> v2
prettyOp op@(LT ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "<" <++> v2
prettyOp op@(LTE ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "<=" <++> v2
prettyOp op@(EQ ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "==" <++> v2
prettyOp op@(GTE ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) ">=" <++> v2
prettyOp op@(GT ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) ">" <++> v2
prettyOp op@StrLength [v] = annotate (Fun $ UN $ Basic $ show op) "length" <++> v
prettyOp op@StrHead [v] = annotate (Fun $ UN $ Basic $ show op) "head" <++> v
prettyOp op@StrTail [v] = annotate (Fun $ UN $ Basic $ show op) "tail" <++> v
prettyOp op@StrIndex [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "[" <+> v2 <+> annotate (Fun $ UN $ Basic $ show op) "]"
prettyOp op@StrCons [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "::" <++> v2
prettyOp op@StrAppend [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "++" <++> v2
prettyOp op@StrReverse [v] = annotate (Fun $ UN $ Basic $ show op) "reverse" <++> v
prettyOp op@StrSubstr [v1,v2,v3] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "[" <+> v2 <+> annotate (Fun $ UN $ Basic $ show op) "," <++> v3 <+> annotate (Fun $ UN $ Basic $ show op) "]"
prettyOp op@DoubleExp [v] = annotate (Fun $ UN $ Basic $ show op) "exp" <++> v
prettyOp op@DoubleLog [v] = annotate (Fun $ UN $ Basic $ show op) "log" <++> v
prettyOp op@DoublePow [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "`pow`" <++> v2
prettyOp op@DoubleSin [v] = annotate (Fun $ UN $ Basic $ show op) "sin" <++> v
prettyOp op@DoubleCos [v] = annotate (Fun $ UN $ Basic $ show op) "cos" <++> v
prettyOp op@DoubleTan [v] = annotate (Fun $ UN $ Basic $ show op) "tan" <++> v
prettyOp op@DoubleASin [v] = annotate (Fun $ UN $ Basic $ show op) "asin" <++> v
prettyOp op@DoubleACos [v] = annotate (Fun $ UN $ Basic $ show op) "acos" <++> v
prettyOp op@DoubleATan [v] = annotate (Fun $ UN $ Basic $ show op) "atan" <++> v
prettyOp op@DoubleSqrt [v] = annotate (Fun $ UN $ Basic $ show op) "sqrt" <++> v
prettyOp op@DoubleFloor [v] = annotate (Fun $ UN $ Basic $ show op) "floor" <++> v
prettyOp op@DoubleCeiling [v] = annotate (Fun $ UN $ Basic $ show op) "ceiling" <++> v
prettyOp op@(Cast x y) [v] = annotate (Fun $ UN $ Basic $ show op) "[" <+> pretty x <++> annotate (Fun $ UN $ Basic $ show op) "->" <++> pretty y <+> annotate (Fun $ UN $ Basic $ show op) "]" <++> v
prettyOp op@BelieveMe [v1,v2,v3] = annotate (Fun $ UN $ Basic $ show op) "believe_me" <++> v1 <++> v2 <++> v3
prettyOp op@Crash [v1,v2] = annotate (Fun $ UN $ Basic $ show op) "crash" <++> v1 <++> v2
