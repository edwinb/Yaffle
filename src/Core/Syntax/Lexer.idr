module Core.Syntax.Lexer

-- Lexer for the basic TT syntax
-- Mostly directly ported from the Idris2 lexer with irrelevant parts
-- removed. I've left mutual blocks for now (TODO: ideally, remove them!)

import Core.TT.Name

import Data.Either
import Data.Maybe
import Data.String

import Libraries.Data.String.Extra
import Libraries.Text.Lexer
import Libraries.Text.Bounded
import public Libraries.Text.Lexer.Tokenizer
import Libraries.Utils.Octal
import Libraries.Utils.String

import Parser.Lexer.Common
import Protocol.Hex

public export
data Token
  -- Literals
  = CharLit String
  | DoubleLit Double
  | IntegerLit Integer
  -- String
  | StringLit Nat String
  -- Identifiers
  | HoleIdent String
  | Ident String
  | DotSepIdent Namespace String -- ident.ident
  | DotIdent String               -- .ident
  | Symbol String
  -- Whitespace
  | Space
  -- Comments
  | Comment
  -- Special
  | EndInput
  | Keyword String
  | Unrecognised String

export
Show Token where
  -- Literals
  show (CharLit x) = "character " ++ show x
  show (DoubleLit x) = "double " ++ show x
  show (IntegerLit x) = "literal " ++ show x
  -- String
  show (StringLit n x) = "string" ++ replicate n '#' ++ " " ++ show x
  -- Identifiers
  show (HoleIdent x) = "hole identifier " ++ x
  show (Ident x) = "identifier " ++ x
  show (DotSepIdent ns n) = "namespaced identifier " ++ show ns ++ "." ++ show n
  show (DotIdent x) = "dot+identifier " ++ x
  show (Symbol x) = "symbol " ++ x
  -- Whitespace
  show Space = "whitespace"
  -- Comments
  show Comment = "comment"
  -- Special
  show EndInput = "end of input"
  show (Keyword x) = x
  show (Unrecognised x) = "Unrecognised " ++ x

mutual
  ||| The mutually defined functions represent different states in a
  ||| small automaton.
  ||| `toEndComment` is the default state and it will munch through
  ||| the input until we detect a special character (a dash, an
  ||| opening brace, or a double quote) and then switch to the
  ||| appropriate state.
  toEndComment : (k : Nat) -> Recognise (k /= 0)
  toEndComment Z = empty
  toEndComment (S k)
               = some (pred (\c => c /= '-' && c /= '{' && c /= '"'))
                        <+> (eof <|> toEndComment (S k))
             <|> is '{' <+> singleBrace k
             <|> is '-' <+> singleDash k
             <|> stringLit <+> toEndComment (S k)

  ||| After reading a single brace, we may either finish reading an
  ||| opening delimiter or ignore it (e.g. it could be an implicit
  ||| binder).
  singleBrace : (k : Nat) -> Lexer
  singleBrace k
     =  is '-' <+> many (is '-')              -- opening delimiter
               <+> (eof <|> singleDash (S k)) -- `singleDash` handles the {----} special case
                                              -- `eof` handles the file ending with {---
    <|> toEndComment (S k)                    -- not a valid comment

  ||| After reading a single dash, we may either find another one,
  ||| meaning we may have started reading a line comment, or find
  ||| a closing brace meaning we have found a closing delimiter.
  singleDash : (k : Nat) -> Lexer
  singleDash k
     =  is '-' <+> doubleDash k    -- comment or closing delimiter
    <|> is '}' <+> toEndComment k  -- closing delimiter
    <|> toEndComment (S k)         -- not a valid comment

  ||| After reading a double dash, we are potentially reading a line
  ||| comment unless the series of uninterrupted dashes is ended with
  ||| a closing brace in which case it is a closing delimiter.
  doubleDash : (k : Nat) -> Lexer
  doubleDash k = with Prelude.(::)
      many (is '-') <+> choice            -- absorb all dashes
        [ is '}' <+> toEndComment k                      -- closing delimiter
        , many (isNot '\n') <+> toEndComment (S k)       -- line comment
        ]

blockComment : Lexer
blockComment = is '{' <+> is '-' <+> many (is '-') <+> (eof <|> toEndComment 1)

docComment : Lexer
docComment = is '|' <+> is '|' <+> is '|' <+> many (isNot '\n')

holeIdent : Lexer
holeIdent = is '?' <+> identNormal

dotIdent : Lexer
dotIdent = is '.' <+> identNormal

pragma : Lexer
pragma = is '%' <+> identNormal

doubleLit : Lexer
doubleLit
    = digits <+> is '.' <+> digits <+> opt
           (is 'e' <+> opt (is '-' <|> is '+') <+> digits)

stringBegin : Lexer
stringBegin = many (is '#') <+> (is '"')

stringEnd : Nat -> String
stringEnd hashtag = "\"" ++ replicate hashtag '#'

public export
keywords : List String
keywords = ["data", "auto", "default", "implicit",
            "lam", "let", "pi", "Type",
            "impossible", "case", "forall", "public", "export", "private",
            "total", "partial", "covering"]

validSymbol : Lexer
validSymbol = some (pred isOpChar)

reservedSymbol : Lexer
reservedSymbol = pred (`elem` ['(', ')', ':'])

fromBinLit : String -> Integer
fromBinLit str
    = if length str <= 2
         then 0
         else let num = assert_total (strTail (strTail str)) in
                fromBin . reverse . map castBin . unpack $ num
    where
      castBin : Char -> Integer
      castBin '1' = 1; castBin _ = 0 -- This can only be '1' and '0' once lexed
      fromBin : List Integer -> Integer
      fromBin [] = 0
      fromBin (0 :: xs) = 2 * fromBin xs
      fromBin (x :: xs) = x + (2 * fromBin xs)

fromHexLit : String -> Integer
fromHexLit str
  = if length str <= 2
       then 0
       else let num = assert_total (strTail (strTail str)) in
             fromMaybe 0 (fromHex (reverse num))
             --        ^-- can't happen if the literal was lexed correctly

fromOctLit : String -> Integer
fromOctLit str
  = if length str <= 2
       then 0
       else let num = assert_total (strTail (strTail str)) in
             fromMaybe 0 (fromOct (reverse num))
             --        ^-- can't happen if the literal lexed correctly

mutual
  rawTokens : Tokenizer Token
  rawTokens =
          match comment (const Comment)
      <|> match blockComment (const Comment)
      <|> match holeIdent (\x => HoleIdent (assert_total (strTail x)))
      <|> match doubleLit (DoubleLit . cast)
      <|> match binUnderscoredLit (IntegerLit . fromBinLit . removeUnderscores)
      <|> match hexUnderscoredLit (IntegerLit . fromHexLit . removeUnderscores)
      <|> match octUnderscoredLit (IntegerLit . fromOctLit . removeUnderscores)
      <|> match digitsUnderscoredLit (IntegerLit . cast . removeUnderscores)
      <|> match charLit (CharLit . stripQuotes)
      <|> match dotIdent (\x => DotIdent (assert_total $ strTail x))
      <|> match namespacedIdent parseNamespace
      <|> match identNormal parseIdent
      <|> match space (const Space)
      <|> match validSymbol Symbol
      <|> match reservedSymbol Symbol
      <|> match symbol Unrecognised
    where
      parseIdent : String -> Token
      parseIdent x = if x `elem` keywords then Keyword x
                     else Ident x

      parseNamespace : String -> Token
      parseNamespace ns = case mkNamespacedIdent ns of
                               (Nothing, ident) => parseIdent ident
                               (Just ns, n)     => DotSepIdent ns n

      countHashtag : String -> Nat
      countHashtag = count (== '#') . unpack

      removeOptionalLeadingSpace : String -> String
      removeOptionalLeadingSpace str = case strM str of
                                            StrCons ' ' tail => tail
                                            _ => str

      removeUnderscores : String -> String
      removeUnderscores s = fastPack $ filter (/= '_') (fastUnpack s)

export
lexTo : Lexer ->
        String ->
        Either (StopReason, Int, Int, String)
               ( List (WithBounds ())     -- bounds of comments
               , List (WithBounds Token)) -- tokens
lexTo reject str
    = case lexTo reject rawTokens str of
           (toks, (EndInput, l, c, _)) =>
             -- Add the EndInput token so that we'll have a line and column
             -- number to read when storing spans in the file
             let end = [MkBounded EndInput False (MkBounds l c l c)] in
             Right $ map (++ end)
                   $ partitionEithers
                   $ map spotComment
                   $ filter isNotSpace toks
           (_, fail) => Left fail
    where

      isNotSpace : WithBounds Token -> Bool
      isNotSpace t = case t.val of
        Space => False
        _ => True

      spotComment : WithBounds Token ->
                    Either (WithBounds ()) (WithBounds Token)
      spotComment t = case t.val of
        Comment => Left (() <$ t)
        _ => Right t

export
lex : String ->
      Either (StopReason, Int, Int, String)
             ( List (WithBounds ())     -- bounds of comments
             , List (WithBounds Token)) -- tokens
lex = lexTo (pred $ const False)
