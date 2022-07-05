module Core.Context.Log

import Core.Context
import Core.Core
import Core.Options
import Core.TT

import Libraries.Data.StringMap

import Data.String
import System.Clock

%default covering

-- if this function is called, then logging must be enabled.
%inline
export
logString : String -> Nat -> String -> CoreE err ()
logString "" n msg = coreLift $ putStrLn
    $ "LOG " ++ show n ++ ": " ++ msg
logString str n msg = coreLift $ putStrLn
    $ "LOG " ++ str ++ ":" ++ show n ++ ": " ++ msg

%inline
export
logString' : LogLevel -> String -> CoreE err ()
logString' lvl =
  logString (fastConcat (intersperse "." (topics lvl)) ++ ":")
            (verbosity lvl)

export
logging' : {auto c : Ref Ctxt Defs} ->
           LogLevel -> CoreE err Bool
logging' lvl = do
    opts <- getSession
    pure $ verbosity lvl == 0 || (logEnabled opts && keepLog lvl (logLevel opts))

export
unverifiedLogging : {auto c : Ref Ctxt Defs} ->
                    String -> Nat -> CoreE err Bool
unverifiedLogging str Z = pure True
unverifiedLogging str n = do
    opts <- getSession
    pure $ logEnabled opts && keepLog (mkUnverifiedLogLevel str n) (logLevel opts)

%inline
export
logging : {auto c : Ref Ctxt Defs} ->
          (s : String) -> {auto 0 _ : KnownTopic s} ->
          Nat -> CoreE err Bool
logging str n = unverifiedLogging str n

||| Log message with a term, translating back to human readable names first.
export
logTerm : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          (s : String) ->
          {auto 0 _ : KnownTopic s} ->
          Nat -> Lazy String -> Term vars -> Core ()
logTerm str n msg tm
    = when !(logging str n)
        $ do tm' <- toFullNames tm
             logString str n $ msg ++ ": " ++ show tm'

export
log' : {auto c : Ref Ctxt Defs} ->
       LogLevel -> Lazy String -> CoreE err ()
log' lvl msg
    = when !(logging' lvl)
        $ logString' lvl msg

||| Log a message with the given log level. Use increasingly
||| high log level numbers for more granular logging.
export
log : {auto c : Ref Ctxt Defs} ->
      (s : String) ->
      {auto 0 _ : KnownTopic s} ->
      Nat -> Lazy String -> CoreE err ()
log str n msg
    = when !(logging str n)
        $ logString str n msg

export
unverifiedLogC : {auto c : Ref Ctxt Defs} ->
                 (s : String) ->
                 Nat -> CoreE err String -> CoreE err ()
unverifiedLogC str n cmsg
    = when !(unverifiedLogging str n)
        $ do msg <- cmsg
             logString str n msg

%inline
export
logC : {auto c : Ref Ctxt Defs} ->
       (s : String) ->
       {auto 0 _ : KnownTopic s} ->
       Nat -> CoreE err String -> CoreE err ()
logC str = unverifiedLogC str

nano : Integer
nano = 1000000000

micro : Integer
micro = 1000000

export
logTimeOver : Integer -> CoreE err String -> CoreE err a -> CoreE err a
logTimeOver nsecs str act
    = do clock <- coreLift (clockTime Process)
         let t = seconds clock * nano + nanoseconds clock
         res <- act
         clock <- coreLift (clockTime Process)
         let t' = seconds clock * nano + nanoseconds clock
         let time = t' - t
         when (time > nsecs) $
           assert_total $ -- We're not dividing by 0
              do str' <- str
                 coreLift $ putStrLn $ "TIMING " ++ str' ++ ": " ++
                          show (time `div` nano) ++ "." ++
                          addZeros (unpack (show ((time `mod` nano) `div` micro))) ++
                          "s"
         pure res
  where
    addZeros : List Char -> String
    addZeros [] = "000"
    addZeros [x] = "00" ++ cast x
    addZeros [x,y] = "0" ++ cast x ++ cast y
    addZeros str = pack str

export
logTimeWhen : {auto c : Ref Ctxt Defs} ->
              Bool -> Nat -> Lazy String -> Core a -> Core a
logTimeWhen p lvl str act
    = if p
         then do clock <- coreLift (clockTime Process)
                 let t = seconds clock * nano + nanoseconds clock
                 res <- act
                 clock <- coreLift (clockTime Process)
                 let t' = seconds clock * nano + nanoseconds clock
                 let time = t' - t
                 assert_total $ -- We're not dividing by 0
                    coreLift $ do
                      let header = "TIMING " ++ replicate lvl '+' ++ ifThenElse (0 < lvl) " " ""
                      putStrLn $ header ++ str ++ ": " ++
                             show (time `div` nano) ++ "." ++
                             addZeros (unpack (show ((time `mod` nano) `div` micro))) ++
                             "s"
                 pure res
         else act
  where
    addZeros : List Char -> String
    addZeros [] = "000"
    addZeros [x] = "00" ++ cast x
    addZeros [x,y] = "0" ++ cast x ++ cast y
    addZeros str = pack str

export
logTime : {auto c : Ref Ctxt Defs} ->
          Nat -> Lazy String -> Core a -> Core a
logTime lvl str act
    = do opts <- getSession
         logTimeWhen (maybe False (lvl <=) (logTimings opts)) lvl str act
