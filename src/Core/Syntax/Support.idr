module Core.Syntax.Support

import Core.Syntax.Lexer
import Core.TT

import public Libraries.Text.Parser
import Libraries.Data.String.Extra

import Data.String

public export
EmptyRule : Type -> Type
EmptyRule = Grammar () Token False

public export
Rule : Type -> Type
Rule = Grammar () Token True

export
symbol : String -> Rule ()
symbol req
    = terminal ("Expected '" ++ req ++ "'") $
               \case
                 Symbol s => guard (s == req)
                 _ => Nothing

export
keyword : String -> Rule ()
keyword req
    = terminal ("Expected '" ++ req ++ "'") $
               \case
                 Keyword s => guard (s == req)
                 _ => Nothing

export
basicIdent : Rule String
basicIdent
    = terminal ("Expected identifier") $
               \case
                 Ident s => pure s
                 _ => Nothing

export
exactIdent : String -> Rule ()
exactIdent req
    = terminal ("Expected " ++ req) $
               \case
                 Ident s => guard (s == req)
                 _ => Nothing

export
eoi : EmptyRule ()
eoi = ignore $ nextIs "Expected end of input" isEOI
  where
    isEOI : Token -> Bool
    isEOI EndInput = True
    isEOI _ = False

export
hex : Char -> Maybe Int
hex '0' = Just 0
hex '1' = Just 1
hex '2' = Just 2
hex '3' = Just 3
hex '4' = Just 4
hex '5' = Just 5
hex '6' = Just 6
hex '7' = Just 7
hex '8' = Just 8
hex '9' = Just 9
hex 'a' = Just 10
hex 'b' = Just 11
hex 'c' = Just 12
hex 'd' = Just 13
hex 'e' = Just 14
hex 'f' = Just 15
hex _ = Nothing

export
dec : Char -> Maybe Int
dec '0' = Just 0
dec '1' = Just 1
dec '2' = Just 2
dec '3' = Just 3
dec '4' = Just 4
dec '5' = Just 5
dec '6' = Just 6
dec '7' = Just 7
dec '8' = Just 8
dec '9' = Just 9
dec _ = Nothing

export
oct : Char -> Maybe Int
oct '0' = Just 0
oct '1' = Just 1
oct '2' = Just 2
oct '3' = Just 3
oct '4' = Just 4
oct '5' = Just 5
oct '6' = Just 6
oct '7' = Just 7
oct _ = Nothing

export
getEsc : String -> Maybe Char
getEsc "NUL" = Just '\NUL'
getEsc "SOH" = Just '\SOH'
getEsc "STX" = Just '\STX'
getEsc "ETX" = Just '\ETX'
getEsc "EOT" = Just '\EOT'
getEsc "ENQ" = Just '\ENQ'
getEsc "ACK" = Just '\ACK'
getEsc "BEL" = Just '\BEL'
getEsc "BS" = Just '\BS'
getEsc "HT" = Just '\HT'
getEsc "LF" = Just '\LF'
getEsc "VT" = Just '\VT'
getEsc "FF" = Just '\FF'
getEsc "CR" = Just '\CR'
getEsc "SO" = Just '\SO'
getEsc "SI" = Just '\SI'
getEsc "DLE" = Just '\DLE'
getEsc "DC1" = Just '\DC1'
getEsc "DC2" = Just '\DC2'
getEsc "DC3" = Just '\DC3'
getEsc "DC4" = Just '\DC4'
getEsc "NAK" = Just '\NAK'
getEsc "SYN" = Just '\SYN'
getEsc "ETB" = Just '\ETB'
getEsc "CAN" = Just '\CAN'
getEsc "EM" = Just '\EM'
getEsc "SUB" = Just '\SUB'
getEsc "ESC" = Just '\ESC'
getEsc "FS" = Just '\FS'
getEsc "GS" = Just '\GS'
getEsc "RS" = Just '\RS'
getEsc "US" = Just '\US'
getEsc "SP" = Just '\SP'
getEsc "DEL" = Just '\DEL'
getEsc str = Nothing

escape' : List Char -> List Char -> Maybe (List Char)
escape' _ [] = pure []
escape' escapeChars (x::xs)
    = assert_total $ if escapeChars `isPrefixOf` (x::xs)
         then case drop (length escapeChars) (x::xs) of
                   ('\\' :: xs) => pure $ '\\' :: !(escape' escapeChars xs)
                   ('\n' :: xs) => pure !(escape' escapeChars xs)
                   ('&' :: xs) => pure !(escape' escapeChars xs)
                   ('a' :: xs) => pure $ '\a' :: !(escape' escapeChars xs)
                   ('b' :: xs) => pure $ '\b' :: !(escape' escapeChars xs)
                   ('f' :: xs) => pure $ '\f' :: !(escape' escapeChars xs)
                   ('n' :: xs) => pure $ '\n' :: !(escape' escapeChars xs)
                   ('r' :: xs) => pure $ '\r' :: !(escape' escapeChars xs)
                   ('t' :: xs) => pure $ '\t' :: !(escape' escapeChars xs)
                   ('v' :: xs) => pure $ '\v' :: !(escape' escapeChars xs)
                   ('\'' :: xs) => pure $ '\'' :: !(escape' escapeChars xs)
                   ('"' :: xs) => pure $ '"' :: !(escape' escapeChars xs)
                   ('x' :: xs) => case span isHexDigit xs of
                                       ([], rest) => escape' escapeChars rest
                                       (ds, rest) => pure $ cast !(toHex 1 (reverse ds)) ::
                                                             !(escape' escapeChars rest)
                   ('o' :: xs) => case span isOctDigit xs of
                                       ([], rest) => escape' escapeChars rest
                                       (ds, rest) => pure $ cast !(toOct 1 (reverse ds)) ::
                                                             !(escape' escapeChars rest)
                   xs => case span isDigit xs of
                              ([], (a :: b :: c :: rest)) =>
                                case getEsc (fastPack [a, b, c]) of
                                     Just v => Just (v :: !(escape' escapeChars rest))
                                     Nothing => case getEsc (fastPack [a, b]) of
                                                     Just v => Just (v :: !(escape' escapeChars (c :: rest)))
                                                     Nothing => escape' escapeChars xs
                              ([], (a :: b :: [])) =>
                                case getEsc (fastPack [a, b]) of
                                     Just v => Just (v :: [])
                                     Nothing => escape' escapeChars xs
                              ([], rest) => escape' escapeChars rest
                              (ds, rest) => Just $ cast (cast {to=Int} (fastPack ds)) ::
                                              !(escape' escapeChars rest)
         else Just $ x :: !(escape' escapeChars xs)
  where
    toHex : Int -> List Char -> Maybe Int
    toHex _ [] = Just 0
    toHex m (d :: ds)
        = pure $ !(hex (toLower d)) * m + !(toHex (m*16) ds)

    toOct : Int -> List Char -> Maybe Int
    toOct _ [] = Just 0
    toOct m (d :: ds)
        = pure $ !(oct (toLower d)) * m + !(toOct (m*8) ds)

export
escape : Nat -> String -> Maybe String
escape hashtag x = let escapeChars = '\\' :: replicate hashtag '#' in
                       fastPack <$> (escape' escapeChars (unpack x))

export
getCharLit : String -> Maybe Char
getCharLit str
   = do e <- escape 0 str
        if length e == 1
           then Just (assert_total (prim__strHead e))
           else if length e == 0 -- parsed the NULL character that terminated the string!
                   then Just '\0000'
                   else Nothing

export
constant : Rule Constant
constant
    = terminal "Expected constant" $ \case
        CharLit c    => Ch <$> getCharLit c
        DoubleLit d  => Just (Db d)
        IntegerLit i => Just (BI i)
        Ident s      => isConstantType (UN $ Basic s) >>=
                             \case WorldType => Nothing
                                   c         => Just $ PrT c
        _            => Nothing

export
intLit : Rule Integer
intLit
    = terminal "Expected integer literal" $
               \case
                 IntegerLit i => Just i
                 _ => Nothing
