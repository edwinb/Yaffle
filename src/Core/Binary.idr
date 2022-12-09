module Core.Binary

import public Core.Binary.Prims
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

||| TTC files can only be compatible if the version number is the same
||| (Update this when changing anything in the data format)
export
ttcVersion : Int
ttcVersion
  = 20221207 -- the date of the update
    * 1000   -- so as to be bigger than Idris 2!
    + 0      -- update number on given date

||| Get a file's modified time. If it doesn't exist, return 0 (UNIX Epoch)
export
modTime : String -> CoreE err Int
modTime fname
  = do Right f <- coreLift $ openFile fname Read
         | Left err => pure 0 -- Beginning of Time :)
       Right t <- coreLift $ fileModifiedTime f
         | Left err => do coreLift $ closeFile f
                          pure 0
       coreLift $ closeFile f
       pure t

makeSTable : Int -> List (String, Int) -> CoreTTC (Binary Write)
makeSTable size xs
    = do st <- newRef STable stInit
         newbuf <- initBinaryS st size
         len <- toBuf {a = Int} (cast (length xs))
         traverse_ addEntry xs
         get Bin
  where
    addEntry : Ref Bin (Binary Write) => (String, Int) -> CoreTTC ()
    addEntry (s, i)
        = do toBuf @{RawString} s
             toBuf i

-- Write out a string table, using 'RawString' TTC instance, because we can't
-- refer to the string table here! It's convenient to use toBuf anyway.
-- Write as a single binary blob, to allow skipping it if we don't need it,
-- e.g. when just reading a prefix of a file to get its dependencies
writeSTableData : Ref Bin (Binary Write) =>
                  Int -> List (String, Int) -> CoreTTC ()
writeSTableData size xs
    = do st <- makeSTable size xs
         toBuf st

readSTableData : Ref Bin (Binary Read) =>
                 CoreTTC (List (Int, String))
readSTableData
    = do bin <- fromBuf
         b <- newRef Bin bin
         len <- fromBuf {b} {a = Int}
         readElems b [] (integerToNat (cast len))
  where
    readElems : Ref Bin (Binary Read) ->
                List (Int, String) -> Nat -> CoreTTC (List (Int, String))
    readElems b xs Z = pure xs -- no need to reverse, order doesn't matter
    readElems b xs (S k)
        = do str <- fromBuf @{RawString} {b}
             i <- fromBuf {b}
             -- Keyed the other way when reading, so swap values
             readElems b ((i, str) :: xs) k

skipSTableData : Ref Bin (Binary Read) =>
                 CoreTTC ()
skipSTableData
    = do bin <- fromBuf {a = Binary Read}
         pure ()

export
writeToFile : (headerID : String) -> -- TT2 or TTM
              (hash : Int) -> -- an interface hash (0 for TTMs)
              (fname : String) -> Binary Write -> CoreTTC (Either FileError ())
writeToFile hdr hash fname bdata
    -- We need to create a new buffer which holds:
    -- * a header 'TTC [version]'
    -- * The string table from 'bdata'
    -- * The actual data in 'bdata'
    -- Then that's the thing we write to disk
    = do let st = table bdata
         tbl <- get STable
         newbuf <- initBinaryS st (used bdata * 2)
         toBuf @{RawString} hdr -- same as Idris 2, so the version error message works
         toBuf @{Wasteful} ttcVersion
         toBuf hash
         writeSTableData (used bdata) (toList (stringIndex tbl))
         toBuf bdata

         outputData <- get Bin
         Right ok <- coreLift $
                       writeBufferToFile fname
                                         (buf outputData) (used outputData)
               | Left (err, size) => pure (Left err)
         pure (Right ok)

export
readFromFile : (headerID : String) -> -- TTM or TT2
               (fname : String) ->
               CoreTTC (Either FileError (Binary Read, Int))
readFromFile hdr fname
    -- Inverse of above. We read:
    -- * a header 'TTC [version]'
    -- * The string table from 'bdata'
    -- * The actual data in 'bdata'
    -- Then create a new Binary Read with all of this data
    = do Right b <- coreLift $ createBufferFromFile fname
               | Left err => pure (Left err)
         bsize <- coreLift $ rawSize b
         stRef <- newRef STable empty
         let filebuf = MkBin b stRef 0 bsize bsize
         bin <- newRef Bin filebuf
         -- Check header is okay
         hdrR <- fromBuf @{RawString}
         version <- fromBuf @{Wasteful}
         hash <- fromBuf
         -- Check format and version here
         when (hdrR /= hdr) $
              corrupt $ hdr ++ " header"
         when (version /= ttcVersion) $
              throw (Format fname version ttcVersion)

         stData <- readSTableData
         bdata <- fromBuf {a = Binary Read}
         stRef <- newRef STable (fromList stData)
         pure (Right (MkBin (buf bdata) stRef
                            0 (used bdata) (used bdata), hash))

-- Read a file, but don't process the String Table because we don't intend
-- to use it.
-- This is for a situation where we just want to process a prefix of the
-- data in the file
export
readNoStringTable : (headerID : String) -> -- TTM or TT2
                    (fname : String) ->
                    CoreTTC (Either FileError (Binary Read))
readNoStringTable hdr fname
    -- Inverse of above. We read:
    -- * a header 'TTC [version]'
    -- * The string table from 'bdata'
    -- * The actual data in 'bdata'
    -- Then create a new Binary Read with all of this data
    = do Right b <- coreLift $ createBufferFromFile fname
               | Left err => pure (Left err)
         bsize <- coreLift $ rawSize b
         stRef <- newRef STable empty
         let filebuf = MkBin b stRef 0 bsize bsize
         bin <- newRef Bin filebuf
         -- Check header is okay
         hdrR <- fromBuf @{RawString}
         version <- fromBuf @{Wasteful}
         hash <- fromBuf {a=Int}
         -- Check format and version here
         when (hdrR /= hdr) $
              corrupt $ hdr ++ " header"
         when (version /= ttcVersion) $
              throw (Format fname version ttcVersion)

         skipSTableData
         bdata <- fromBuf {a = Binary Read}
         pure (Right (MkBin (buf bdata) stRef
                            0 (used bdata) (used bdata)))

-- Process just enough to get the hash (usually, the interface hash to see
-- if we need to rebuild a dependency) from a file
export
readHash : (headerID : String) -> -- TTM or TT2
           (fname : String) ->
           CoreTTC (Either FileError Int)
readHash hdr fname
    = do Right b <- coreLift $ createBufferFromFile fname
               | Left err => pure (Left err)
         bsize <- coreLift $ rawSize b
         stRef <- newRef STable empty
         let filebuf = MkBin b stRef 0 bsize bsize
         bin <- newRef Bin filebuf
         -- Check header is okay
         hdrR <- fromBuf @{RawString}
         version <- fromBuf @{Wasteful}
         hash <- fromBuf
         pure (Right hash)
