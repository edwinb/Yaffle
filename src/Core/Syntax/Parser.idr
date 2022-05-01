module Core.Syntax.Parser

-- A parser for raw TT terms, in an S-expression type syntex
-- Uses its own lexer (not the full Idris lexer) since it's a much simpler
-- language, and only for testing/experiments.

import Core.Error
import Core.FC
import Core.Syntax.Lexer
import Core.Syntax.Raw
import public Core.Syntax.Support
import Core.TT.Name

import public Libraries.Text.Parser
import Libraries.Data.String.Extra

import Data.String

export
namespacedIdent : Rule (Maybe Namespace, String)
namespacedIdent
    = terminal "Expected namespaced name" $
               \case
                 DotSepIdent ns n => Just (Just ns, n)
                 Ident i => Just (Nothing, i)
                 _ => Nothing

reservedNames : List String
reservedNames
    = [ "Type", "Int", "Int8", "Int16", "Int32", "Int64", "Integer"
      , "Bits8", "Bits16", "Bits32", "Bits64"
      , "String", "Char", "Double", "Lazy", "Inf", "Force", "Delay"
      ]

isNotReservedName : WithBounds String -> EmptyRule ()
isNotReservedName x
    = when (x.val `elem` reservedNames) $
        failLoc x.bounds $ "Can't use reserved name \{x.val}"

name : Rule Name
name = do nsx <- bounds namespacedIdent
          nameNS nsx
 where
  nameNS : WithBounds (Maybe Namespace, String) -> EmptyRule Name
  nameNS nsx = do
    let id = snd <$> nsx
    isNotReservedName id
    pure $ uncurry mkNamespacedName (map Basic nsx.val)

bracketed : Rule a -> Rule a
bracketed r
    = do symbol "("; x <- r; symbol ")"; pure x

rawi : OriginDesc -> Rule RawI
rawc : OriginDesc -> Rule RawC
simpleRawi : OriginDesc -> Rule RawI
simpleRawc : OriginDesc -> Rule RawC

mkApp : FC -> RawI -> List RawC -> RawI
mkApp fc f [] = f
mkApp fc f (x :: xs) = mkApp fc (RApp fc f x) xs

mkApp1 : FC -> RawI -> List1 RawC -> RawI
mkApp1 fc f (arg ::: args) = mkApp fc (RApp fc f arg) args

caseAlt : OriginDesc -> Rule RawCaseAlt
caseAlt fname
    = do symbol "_"
         symbol "=>"
         rhs <- rawc fname
         pure (RDefaultCase rhs)
  <|> do p <- constant
         symbol "=>"
         rhs <- rawc fname
         pure (RConstCase p rhs)
  <|> do n <- name
         args <- many name
         symbol "=>"
         rhs <- rawc fname
         pure (RConCase n args rhs)

simpleRawi fname
    = do var <- bounds name
         pure (RVar (boundToFC fname var) var.val)
  <|> do start <- location
         keyword "Type"
         end <- location
         pure (RType (MkFC fname start end))
  <|> do start <- location
         p <- constant
         end <- location
         pure (RPrimVal (MkFC fname start end) p)
  <|> do start <- location
         symbol "("
         val <- rawc fname
         symbol ":"
         ty <- rawi fname
         symbol ")"
         end <- location
         pure (RAnnot (MkFC fname start end) val ty)
  <|> do start <- location
         keyword "pi"
         n <- name
         symbol ":"
         arg <- rawc fname
         symbol "."
         ret <- rawc fname
         end <- location
         pure (RPi (MkFC fname start end) RigW n arg ret)
  <|> do start <- location
         keyword "let"
         n <- name
         symbol ":"
         ty <- rawc fname
         symbol "="
         val <- rawc fname
         keyword "in"
         sc <- rawi fname
         end <- location
         pure (RLet (MkFC fname start end) RigW n val ty sc)
  <|> do symbol "("
         tm <- rawi fname
         symbol ")"
         pure tm

rawi fname
    = do start <- location
         f <- simpleRawi fname
         args <- many (simpleRawc fname)
         end <- location
         pure $ mkApp (MkFC fname start end) f args

simpleRawc fname
    = do symbol "("
         tm <- rawc fname
         symbol ")"
         pure tm
  <|> do start <- location
         i <- simpleRawi fname -- This breaks the totality checking of the parser!
                         -- I haven't worked out why...
         end <- location
         pure (RInf (MkFC fname start end) i)

rawc fname
    = do start <- location
         keyword "case"
         scr <- rawi fname
         keyword "of"
         alts <- sepBy (symbol "|") (caseAlt fname)
         end <- location
         pure (RCase (MkFC fname start end) scr alts)
  <|> do start <- location
         keyword "lam"
         n <- name
         symbol "."
         sc <- rawc fname
         end <- location
         pure (RLam (MkFC fname start end) n sc)
  <|> do start <- location
         i <- rawi fname -- This breaks the totality checking of the parser!
                         -- I haven't worked out why...
         end <- location
         pure (RInf (MkFC fname start end) i)
  <|> simpleRawc fname

tyDecl : OriginDesc -> Rule RawDecl
tyDecl fname
    = do start <- location
         n <- name
         symbol ":"
         d <- rawc fname
         symbol ";"
         end <- location
         pure (RTyDecl (MkFC fname start end) n d)

conDecl : OriginDesc -> Rule RawCon
conDecl fname
    = do n <- name
         symbol ":"
         d <- rawc fname
         pure (RConDecl n d)

dataDef : OriginDesc -> Rule RawData
dataDef fname
    = do keyword "data"
         n <- name
         symbol ":"
         ty <- rawc fname
         keyword "where"
         symbol "{"
         cons <- sepBy (symbol "|") (conDecl fname)
         symbol "}"
         pure (RDataDecl n ty cons)

dataDecl : OriginDesc -> Rule RawDecl
dataDecl fname
    = do start <- location
         d <- dataDef fname
         end <- location
         pure (RData (MkFC fname start end) d)

fnDef : OriginDesc -> Rule RawDecl
fnDef fname
    = do start <- location
         n <- name
         symbol "="
         d <- rawc fname
         end <- location
         symbol ";"
         pure (RDef (MkFC fname start end) n d)

rawDecl : OriginDesc -> Rule RawDecl
rawDecl fname
     = tyDecl fname
   <|> dataDecl fname
   <|> fnDef fname

export
command : OriginDesc -> Rule Command
command fname
    = do decl <- rawDecl fname
         pure (Decl decl)
  <|> do tm <- rawi fname
         symbol ";"
         pure (Eval tm)

export
rawInput : OriginDesc -> Rule (List Command)
rawInput fname
    = do xs <- some (command fname)
         eoi
         pure (toList xs)

fromLexError : OriginDesc -> (StopReason, Int, Int, String) -> Error
fromLexError origin (ComposeNotClosing begin end, _, _, _)
    = LexFail (MkFC origin begin end) "Bracket is not properly closed."
fromLexError origin (_, l, c, _)
    = LexFail (MkFC origin (l, c) (l, c + 1)) "Can't recognise token."

export
fromParsingErrors : Show token =>
                    OriginDesc -> List1 (ParsingError token) -> Error
fromParsingErrors origin = ParseFail . (map fromError)
  where
    fromError : ParsingError token -> (FC, String)
    fromError (Error msg Nothing)
        = (MkFC origin (0, 0) (0, 0), msg +> '.')
    fromError (Error msg (Just t))
        = let start = startBounds t; end = endBounds t in
            let fc = if start == end
                      then MkFC origin start (mapSnd (+1) start)
                      else MkFC origin start end
            in (fc, msg +> '.')

export
parse : OriginDesc -> Rule a -> String ->
        Either Error a
parse origin rule inp
    = do (cs, toks) <- mapFst (fromLexError origin) $ lex inp
         (decs, ws, (parsed, _)) <- mapFst (fromParsingErrors origin) $
                                           parseWith rule toks
         pure parsed

testf : OriginDesc
testf = PhysicalIdrSrc (nsAsModuleIdent (unsafeFoldNamespace ["hi"]))

testp : String -> Either Error RawI
testp inp = parse testf (rawi testf) inp
