module Libraries.Utils.Binary

import Data.Buffer
import Data.List

import Libraries.Data.IntMap
import Libraries.Data.StringMap
import Libraries.System.File

-- Serialising data as binary, primitive operations.
-- Files are composed of a string table, then a binary blob which may
-- contain pointers into the string table.

%default covering

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

public export
data BinaryMode = Read | Write

export
Show BinaryMode where
  show Read = "Read"
  show Write = "Write"

public export
Table : BinaryMode -> Type
Table Read = IntMap String
Table Write = StringTable

public export
record Binary (m : BinaryMode) where
  constructor MkBin
  buf : Buffer
  table : Table m
  loc : Int
  size : Int -- Capacity
  used : Int -- Amount used

export
newBinary : Buffer -> StringTable -> Int -> Binary Write
newBinary b st s = MkBin b st 0 s 0

export
blockSize : Int
blockSize = 655360

export
avail : Binary Write -> Int
avail c = (size c - loc c) - 1

export
toRead : Binary Read -> Int
toRead c = used c - loc c

export
appended : Int -> Binary Write -> Binary Write
appended i (MkBin b st loc s used) = MkBin b st (loc+i) s (used + i)

export
incLoc : Int -> Binary Read -> Binary Read
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

export
writeToFile : (fname : String) -> Binary Write -> IO (Either FileError ())
-- writeToFile fname c
--     = do Right ok <- writeBufferToFile fname (buf c) (used c)
--                | Left (err, size) => pure (Left err)
--          pure (Right ok)

export
readFromFile : (fname : String) -> IO (Either FileError (Binary Read))
-- readFromFile fname
--     = do Right b <- createBufferFromFile fname
--                | Left err => pure (Left err)
--          bsize <- rawSize b
--          pure (Right (MkBin b 0 bsize bsize))
