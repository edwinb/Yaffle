module Core.Binary.Prims

import Core.Core

import Data.Buffer
import Data.List
import Data.List.Elem
import Data.SnocList
import Data.List1
import Data.Vect

import Libraries.Data.PosMap
import Libraries.Data.IntMap
import Libraries.Data.StringMap
import Libraries.System.File
import Libraries.System.File.Buffer

-- Label for binary states
export
data Bin : Type where

-- Label for string tables
export
data STable : Type where

-- For more efficient reading/writing/sharing of strings, we store strings
-- in a string table, and look them up by int id
public export
record StringTable where
  constructor MkStringTable
  nextIndex : Int
  stringIndex : StringMap Int

export
stInit : StringTable
stInit = MkStringTable { nextIndex = 0, stringIndex = empty }

export
addString : String -> StringTable -> StringTable
addString s tbl
    = case lookup s (stringIndex tbl) of
           Just _ => tbl
           Nothing => let idx = tbl.nextIndex in
                          { nextIndex := idx + 1,
                            stringIndex $= insert s idx } tbl

public export
data BinaryMode = Read | Write

export
Show BinaryMode where
  show Read = "Read"
  show Write = "Write"

export
Eq BinaryMode where
  Read == Read = True
  Write == Write = True
  _ == _ = False

public export
Table : BinaryMode -> Type
Table Read = IntMap String
Table Write = StringTable

public export
data TTCError : Type where
     CantCreateBuffer : TTCError
     CantExpandBuffer : TTCError
     Format : String -> Int -> Int -> TTCError
     EndOfBuffer : String -> TTCError
     Corrupt : String -> TTCError
     BadBinaryMode : BinaryMode -> TTCError

export
Show TTCError where
  show CantCreateBuffer = "TTC buffer creation failed"
  show CantExpandBuffer = "TTC buffer expansion failed"
  show (Format file ver exp) =
    let age = if ver < exp then "older" else "newer" in
        "TTC data is in an " ++ age ++ " format, file: " ++ file ++ ", expected version: " ++ show exp ++ ", actual version: " ++ show ver
  show (EndOfBuffer when) = "End of buffer when reading " ++ when
  show (Corrupt ty) = "Corrupt TTC data for " ++ ty
  show (BadBinaryMode b) = "Internal TTC error in binary mode " ++ show b

export
Eq TTCError where
  CantCreateBuffer == CantCreateBuffer = True
  CantExpandBuffer == CantExpandBuffer = True
  Format x1 y1 z1 == Format x2 y2 z2 = x1 == x2 && y1 == y2 && z1 == z2
  EndOfBuffer x1 == EndOfBuffer x2 = x1 == x2
  Corrupt x1 == Corrupt x2 = x1 == x2
  BadBinaryMode x1 == BadBinaryMode x2 = x1 == x2
  _ == _ = False

public export
CoreTTC : Type -> Type
CoreTTC = CoreE TTCError

public export
record Binary (m : BinaryMode) where
  constructor MkBin
  buf : Buffer
  table : Ref STable (Table m)
  loc : Integer
  size : Integer -- Capacity
  used : Integer -- Amount used

export
newBinary : Buffer -> Ref STable StringTable -> Integer -> Binary Write
newBinary b st s = MkBin b st 0 s 0

%inline export
blockSize : Integer
blockSize = 655360

export
avail : Binary Write -> Integer
avail c = (size c - loc c) - 1

export
toRead : Binary Read -> Integer
toRead c = used c - loc c

export
appended : Integer -> Binary Write -> Binary Write
appended i (MkBin b st loc s used) = MkBin b st (loc+i) s (used + i)

export
incLoc : Integer -> Binary Read -> Binary Read
incLoc i c = { loc $= (+i) } c

export
dumpBin : Binary m -> IO ()
dumpBin chunk
   = do -- printLn !(traverse bufferData (map buf done))
        printLn !(bufferData (buf chunk))
        -- printLn !(traverse bufferData (map buf rest))

export
nonEmptyRev : {xs : _} ->
              NonEmpty (xs ++ y :: ys)
nonEmptyRev {xs = []} = IsNonEmpty
nonEmptyRev {xs = (x :: xs)} = IsNonEmpty

public export
interface TTC a where -- TTC = TT intermediate code/interface file
  -- Add binary data representing the value to the given buffer
  toBuf : Ref Bin (Binary Write) =>
          a -> CoreTTC ()
  -- Return the data representing a thing of type 'a' from the given buffer.
  -- Throws if the data can't be parsed as an 'a'
  fromBuf : (b : Ref Bin (Binary Read)) =>
            CoreTTC a

-- Create a new list of chunks, initialised with one 64k chunk
export
initBinary : Ref STable StringTable -> CoreTTC (Ref Bin (Binary Write))
initBinary st
    = do Just buf <- coreLift $ newBuffer (cast blockSize)
             | Nothing => throw CantCreateBuffer
         newRef Bin (newBinary buf st blockSize)

export
initBinaryS : Ref STable StringTable -> Integer -> CoreTTC (Ref Bin (Binary Write))
initBinaryS st s
    = do Just buf <- coreLift $ newBuffer (cast s)
             | Nothing => throw CantCreateBuffer
         newRef Bin (newBinary buf st s)

extendBinary : Integer -> Binary Write -> CoreTTC (Binary Write)
extendBinary need (MkBin buf st l s u)
    = do let newsize : Integer = s * 2
         let s' = if (newsize - l) < need
                     then newsize + need
                     else newsize
         Just buf' <- coreLift $ resizeBuffer buf (cast s')
             | Nothing => throw CantExpandBuffer
         pure (MkBin buf' st l s' u)

export
corrupt : String -> CoreTTC a
corrupt ty = throw (Corrupt ty)

-- tag and getTag assume the Int is in the range 0-255 (we don't have
-- Bits8 yet!)
export
tag : Ref Bin (Binary Write) => Int -> CoreTTC ()
tag val
    = do chunk <- get Bin
         if avail chunk >= 1
            then
              do coreLift $ setByte (buf chunk) (cast $ loc chunk) val
                 put Bin (appended 1 chunk)
            else do chunk' <- extendBinary 1 chunk
                    coreLift $ setByte (buf chunk') (cast $ loc chunk') val
                    put Bin (appended 1 chunk')

export
getTag : Ref Bin (Binary Read) => CoreTTC Int
getTag
    = do chunk <- get Bin
         if toRead chunk >= 1
            then
              do val <- coreLift $ getByte (buf chunk) (cast $ loc chunk)
                 put Bin (incLoc 1 chunk)
                 pure val
              else throw (EndOfBuffer "Byte")

-- Primitives; these are the only things that have to deal with growing
-- the buffer list

-- Some useful types from the prelude

export
[Wasteful] TTC Int where
  toBuf val
    = do chunk <- get Bin
         if avail chunk >= 8
            then
              do coreLift $ setInt (buf chunk) (cast $ loc chunk) val
                 put Bin (appended 8 chunk)
            else do chunk' <- extendBinary 8 chunk
                    coreLift $ setInt (buf chunk') (cast $ loc chunk') val
                    put Bin (appended 8 chunk')

  fromBuf
    = do chunk <- get Bin
         if toRead chunk >= 8
            then
              do val <- coreLift $ getInt (buf chunk) (cast $ loc chunk)
                 put Bin (incLoc 8 chunk)
                 pure val
              else throw (EndOfBuffer ("Int " ++ show (loc chunk, size chunk)))

export
TTC Int where
  toBuf val
    = if val >= -127 && val < 128
         then tag (val + 127)
         else do tag 255
                 chunk <- get Bin
                 if avail chunk >= 8
                    then
                      do coreLift $ setInt (buf chunk) (cast $ loc chunk) val
                         put Bin (appended 8 chunk)
                    else do chunk' <- extendBinary 8 chunk
                            coreLift $ setInt (buf chunk') (cast $ loc chunk') val
                            put Bin (appended 8 chunk')

  fromBuf
    = case !getTag of
           255 => do chunk <- get Bin
                     if toRead chunk >= 8
                       then
                         do val <- coreLift $ getInt (buf chunk) (cast $ loc chunk)
                            put Bin (incLoc 8 chunk)
                            pure val
                       else throw (EndOfBuffer ("Int " ++ show (loc chunk, size chunk)))
           t => pure (t - 127)

export
[RawString] TTC String where
  toBuf val
      -- To support UTF-8 strings, this has to get the length of the string
      -- in bytes, not the length in characters.
      = do let ireq = stringByteLength val
           let req : Integer = cast ireq
           toBuf ireq
           chunk <- get Bin
           if avail chunk >= req
              then
                do coreLift $ setString (buf chunk) (cast $ loc chunk) val
                   put Bin (appended req chunk)
              else do chunk' <- extendBinary req chunk
                      coreLift $ setString (buf chunk') (cast $ loc chunk') val
                      put Bin (appended req chunk')

  fromBuf
      = do ilen <- fromBuf {a = Int}
           let len = cast ilen
           chunk <- get Bin
           when (len < 0) $ corrupt "RawString"
           if toRead chunk >= len
              then
                do val <- coreLift $ getString (buf chunk) (cast $ loc chunk) ilen
                   put Bin (incLoc len chunk)
                   pure val
              else throw (EndOfBuffer ("String length " ++ show len ++
                                       " at " ++ show (loc chunk)))

export
TTC String where
  toBuf str
      = do b <- get Bin
           let tblRef = table b
           tbl <- get STable
           case lookup str (stringIndex tbl) of
                Nothing => do let idx' = nextIndex tbl
                              let si' = insert str idx' (stringIndex tbl)
                              let tbl' : Table Write
                                       = { nextIndex := idx' + 1,
                                           stringIndex := si' } tbl
                              put STable tbl'
                              toBuf idx'
                Just val => toBuf val

  fromBuf
      = do b <- get Bin
           let tblRef = table b
           tbl <- get STable
           idx <- fromBuf
           case lookup idx tbl of
                Nothing => do coreLift $ printLn (IntMap.toList tbl)
                              corrupt ("StringTable entry " ++ show idx)
                Just str => pure str

-- When reading/writing binary, we assume that the inner Binary inherits the
-- string table of the outer binary
export
TTC (Binary Write) where
  toBuf val
    = do let len = used val
         let ilen : Int = cast len
         toBuf ilen
         chunk <- get Bin
         if avail chunk >= len
            then
              do coreLift $ copyData (buf val) 0 ilen
                                     (buf chunk) (cast $ loc chunk)
                 put Bin (appended len chunk)
            else do chunk' <- extendBinary len chunk
                    coreLift $ copyData (buf val) 0 ilen
                                        (buf chunk') (cast $ loc chunk')
                    put Bin (appended len chunk')

  fromBuf = throw (BadBinaryMode Write)

export
TTC (Binary Read) where
  toBuf val = throw (BadBinaryMode Read)

  fromBuf
    = do ilen <- fromBuf
         let len : Integer = cast ilen
         chunk <- get Bin
         if toRead chunk >= len
            then
              do Just newbuf <- coreLift $ newBuffer ilen
                      | Nothing => corrupt "Binary"
                 coreLift $ copyData (buf chunk) (cast $ loc chunk) ilen
                                     newbuf 0
                 put Bin (incLoc len chunk)
                 pure (MkBin newbuf (table chunk) 0 len len)
            else throw (EndOfBuffer "Binary")

export
TTC Bool where
  toBuf False = tag 0
  toBuf True = tag 1
  fromBuf
      = case !getTag of
             0 => pure False
             1 => pure True
             _ => corrupt "Bool"

export
TTC Char where
  toBuf c = toBuf (cast {to=Int} c)
  fromBuf
      = do i <- fromBuf
           pure (cast {from=Int} i)

export
TTC Double where
  toBuf val
    = do chunk <- get Bin
         if avail chunk >= 8
            then
              do coreLift $ setDouble (buf chunk) (cast $ loc chunk) val
                 put Bin (appended 8 chunk)
            else do chunk' <- extendBinary 8 chunk
                    coreLift $ setDouble (buf chunk') (cast $ loc chunk') val
                    put Bin (appended 8 chunk')

  fromBuf
    = do chunk <- get Bin
         if toRead chunk >= 8
            then
              do val <- coreLift $ getDouble (buf chunk) (cast $ loc chunk)
                 put Bin (incLoc 8 chunk)
                 pure val
              else throw (EndOfBuffer "Double")

export
(TTC a, TTC b) => TTC (a, b) where
  toBuf (x, y)
     = do toBuf x
          toBuf y
  fromBuf
     = do x <- fromBuf
          y <- fromBuf
          pure (x, y)

export
TTC () where
  toBuf () = pure ()
  fromBuf = pure ()

export
(TTC a, {y : a} -> TTC (p y)) => TTC (DPair a p) where
  toBuf (vs ** tm)
      = do toBuf vs
           toBuf tm

  fromBuf
      = do x <- fromBuf
           p <- fromBuf
           pure (x ** p)

export
TTC a => TTC (Maybe a) where
  toBuf Nothing
     = tag 0
  toBuf (Just val)
     = do tag 1
          toBuf val

  fromBuf
     = case !getTag of
            0 => pure Nothing
            1 => do val <- fromBuf
                    pure (Just val)
            _ => corrupt "Maybe"

export
(TTC a, TTC b) => TTC (Either a b) where
  toBuf (Left val)
     = do tag 0
          toBuf val
  toBuf (Right val)
     = do tag 1
          toBuf val

  fromBuf
     = case !getTag of
            0 => do val <- fromBuf
                    pure (Left val)
            1 => do val <- fromBuf
                    pure (Right val)
            _ => corrupt "Either"

export
TTC a => TTC (List a) where
  toBuf xs
      = do toBuf (TailRec_length xs)
           traverse_ toBuf xs
    where
      ||| Tail-recursive length as buffer sizes can get large
      |||
      ||| Once we port to Idris2, can use Data.List.TailRec.length instead
      length_aux : List a -> Int -> Int
      length_aux [] len = len
      length_aux (_::xs) len = length_aux xs (1 + len)

      TailRec_length : List a -> Int
      TailRec_length xs = length_aux xs 0

  fromBuf
      = do len <- fromBuf {a = Int}
           readElems [] (integerToNat (cast len))
    where
      readElems : List a -> Nat -> CoreTTC (List a)
      readElems xs Z = pure (reverse xs)
      readElems xs (S k)
          = do val <- fromBuf
               readElems (val :: xs) k

export
TTC a => TTC (SnocList a) where
  toBuf xs
      = do toBuf (TailRec_length xs)
           ignore $ traverseSnocList toBuf xs
    where
      ||| Tail-recursive length as buffer sizes can get large
      |||
      ||| Once we port to Idris2, can use Data.List.TailRec.length instead
      length_aux : SnocList a -> Int -> Int
      length_aux [<] len = len
      length_aux (xs :< _) len = length_aux xs (1 + len)

      TailRec_length : SnocList a -> Int
      TailRec_length xs = length_aux xs 0

  fromBuf
      = do len <- fromBuf {a = Int}
           readElems [<] (integerToNat (cast len))
    where
      readElems : SnocList a -> Nat -> CoreTTC (SnocList a)
      readElems xs Z = pure (reverse xs)
      readElems xs (S k)
          = do val <- fromBuf
               readElems (xs :< val) k

export
TTC a => TTC (List1 a) where
  toBuf xxs
     = do toBuf (head xxs)
          toBuf (tail xxs)

  fromBuf = do
    x <- fromBuf
    xs <- fromBuf
    pure (x ::: xs)

export
{n : Nat} -> TTC a => TTC (Vect n a) where
  toBuf xs = writeAll xs
    where
      writeAll : forall n . Vect n a -> CoreTTC ()
      writeAll [] = pure ()
      writeAll (x :: xs) = do toBuf x; writeAll xs

  fromBuf {n} = rewrite sym (plusZeroRightNeutral n) in readElems [] n
    where
      readElems : Vect done a -> (todo : Nat) -> CoreTTC (Vect (todo + done) a)
      readElems {done} xs Z
          = pure (reverse xs)
      readElems {done} xs (S k)
          = do val <- fromBuf
               rewrite (plusSuccRightSucc k done)
               readElems (val :: xs) k

export
(TTC a, Measure a) => TTC (PosMap a) where
  toBuf = toBuf . toList
  fromBuf = fromList <$> fromBuf

%hide Fin.fromInteger

count : List.Elem.Elem x xs -> Int
count Here = 0
count (There p) = 1 + count p

toLimbs : Integer -> List Int
toLimbs x
    = if x == 0
         then []
         else if x == -1 then [-1]
              else fromInteger (prim__and_Integer x 0xffffffff) ::
                   toLimbs (prim__shr_Integer x 32)

fromLimbs : List Int -> Integer
fromLimbs [] = 0
fromLimbs (x :: xs) = cast x + prim__shl_Integer (fromLimbs xs) 32

export
TTC Integer where
  toBuf val
    = assert_total $ if val < 0
         then do tag 0
                 toBuf (toLimbs (-val))
         else do tag 1
                 toBuf (toLimbs val)
  fromBuf
    = do val <- getTag
         case val of
              0 => do val <- fromBuf
                      pure (-(fromLimbs val))
              1 => do val <- fromBuf
                      pure (fromLimbs val)
              _ => corrupt "Integer"

export
TTC Bits8 where
  toBuf x = toBuf $ cast {to = Int} x
  fromBuf = cast {from = Int} <$> fromBuf

export
TTC Bits16 where
  toBuf x = toBuf $ cast {to = Int} x
  fromBuf = cast {from = Int} <$> fromBuf

export
TTC Bits32 where
  toBuf x = toBuf $ cast {to = Integer} x
  fromBuf = cast {from = Integer} <$> fromBuf

export
TTC Bits64 where
  toBuf x = toBuf $ cast {to = Integer} x
  fromBuf = cast {from = Integer} <$> fromBuf

export
TTC Int8 where
  toBuf x = toBuf $ cast {to = Int} x
  fromBuf = cast {from = Int} <$> fromBuf

export
TTC Int16 where
  toBuf x = toBuf $ cast {to = Int} x
  fromBuf = cast {from = Int} <$> fromBuf

export
TTC Int32 where
  toBuf x = toBuf $ cast {to = Int} x
  fromBuf = cast {from = Int} <$> fromBuf

export
TTC Int64 where
  toBuf x = toBuf $ cast {to = Integer} x
  fromBuf = cast {from = Integer} <$> fromBuf

export
TTC Nat where
  toBuf val = toBuf (cast {to=Integer} val)
  fromBuf
     = do val <- fromBuf
          pure (fromInteger val)
