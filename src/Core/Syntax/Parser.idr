module Core.Syntax.Parser

-- A parser for raw TT terms, in an S-expression type syntex
-- Uses its own lexer (not the full Idris lexer) since it's a much simpler
-- language, and only for testing/experiments.

import Core.Error
import Core.FC
import Core.Syntax.Lexer
import Core.Syntax.Raw
import Core.TT.Name

import public Libraries.Text.Parser
import Libraries.Data.String.Extra

public export
EmptyRule : Type -> Type
EmptyRule = Grammar () Token False

public export
Rule : Type -> Type
Rule = Grammar () Token True

symbol : String -> Rule ()
symbol req
    = terminal ("Expected '" ++ req ++ "'") $
               \case
                 Symbol s => guard (s == req)
                 _ => Nothing

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

rawi fname
    = bracketed (do start <- location
                    val <- rawc fname
                    symbol ":"
                    ty <- rawi fname
                    end <- location
                    pure (RAnnot (MkFC fname start end) val ty))
  <|> do var <- bounds name
         pure (RVar (boundToFC fname var) var.val)

rawc fname
    = do i <- bounds $ rawi fname
         pure (RInf (boundToFC fname i) i.val)

rawDecl : OriginDesc -> Rule RawDecl

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

parse : OriginDesc -> Rule a -> String ->
        Either Error a
parse origin rule inp
    = do (cs, toks) <- mapFst (fromLexError origin) $ lex inp
         (decs, ws, (parsed, _)) <- mapFst (fromParsingErrors origin) $
                                           parseWith rule toks
         pure parsed

testf : OriginDesc
testf = PhysicalIdrSrc (nsAsModuleIdent (unsafeFoldNamespace ["hi"]))
