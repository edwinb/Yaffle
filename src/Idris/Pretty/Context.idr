module Idris.Pretty.Context

import Core.Context
import Core.Env

import Data.String
import Idris.Doc.Annotations

import Idris.Syntax
import Idris.Pretty

import Core.Context

import Libraries.Data.String.Extra

%hide String.(::)
%hide String.Nil
%hide Doc.Nil
%hide Stream.(::)
%hide Symbols.equals
%hide String.indent
%hide Extra.indent
%hide List1.(++)
-- %hide SnocList.(++)
%hide String.(++)
%hide Pretty.Syntax
%hide List1.forget

%default covering

namespace Raw
  export
  prettyTree : {vars : _} -> Term vars -> Doc IdrisSyntax
  prettyAlt : {vars : _} -> CaseAlt vars -> Doc IdrisSyntax

{-
  prettyTree (Case {name} idx prf ty alts)
      = let ann = case ty of
                    Erased _ _ => ""
                    _ => space <+> keyword ":" <++> byShow ty
        in case_ <++> annotate Bound (pretty0 name) <+> ann <++> of_
         <+> nest 2 (hardline
         <+> vsep (assert_total (map prettyAlt alts)))
  prettyTree (STerm i tm) = byShow tm
  prettyTree (Unmatched msg) = "Error:" <++> pretty0 msg
  prettyTree Impossible = "Impossible"

  prettyAlt (ConCase n tag args sc)
      = hsep (annotate (DCon (Just n)) (pretty0 n) ::  map pretty0 args)
        <++> fatArrow
        <+> let sc = prettyTree sc in
            Union (spaces 1 <+> sc) (nest 2 (hardline <+> sc))
  prettyAlt (DelayCase _ arg sc) =
        keyword "Delay" <++> pretty0 arg
        <++> fatArrow
        <+> let sc = prettyTree sc in
            Union (spaces 1 <+> sc) (nest 2 (hardline <+> sc))
  prettyAlt (ConstCase c sc) =
        pretty c
        <++> fatArrow
        <+> let sc = prettyTree sc in
            Union (spaces 1 <+> sc) (nest 2 (hardline <+> sc))
  prettyAlt (DefaultCase sc) =
        keyword "_"
        <++> fatArrow
        <+> let sc = prettyTree sc in
            Union (spaces 1 <+> sc) (nest 2 (hardline <+> sc))
            -}

  export
  prettyDef : Def -> Doc IdrisDocAnn
  prettyDef None = "undefined"
  prettyDef (Function _ ct _ pats) =
       let ct = prettyTree ct in
        header "Compile time tree" <++> reAnnotate Syntax ct

  prettyDef (DCon nt tag arity) =
      vcat $ header "Data constructor" :: map (indent 2)
          ([ "tag:" <++> byShow tag
           , "arity:" <++> byShow arity
           ] ++ maybe [] (\ n => ["newtype by:" <++> byShow n]) (newTypeArg nt))
  prettyDef (TCon ti arity) =
        let enum = hsep . punctuate ","
            ps = paramPos ti
            ms = mutWith ti
            det = detagBy ti
            cons = datacons ti in
        vcat $ header "Type constructor" :: map (indent 2)
          ([ "arity:" <++> byShow arity
           , "parameter positions:" <++> byShow ps
           , "constructors:" <++> enum ((\ nm => annotate (Syntax $ DCon (Just nm)) (pretty0 nm)) <$> cons)
           ] ++ (("mutual with:" <++> enum (pretty0 <$> ms)) <$ guard (not $ null ms))
             ++ (maybe [] (\ pos => ["detaggable by:" <++> byShow pos]) det))
  prettyDef (ExternDef arity) =
      vcat $ header "External definition" :: map (indent 2)
           [ "arity:" <++> byShow arity ]
  prettyDef (ForeignDef arity calls) =
     vcat $ header "Foreign definition" :: map (indent 2)
          [ "arity:" <++> byShow arity
          , "bindings:" <++> byShow calls ]
  prettyDef (Hole numlocs hf) =
        vcat $ header "Hole" :: map (indent 2)
          ("Implicitly bound name" <$ guard (implbind hf))
  prettyDef (BySearch rig depth def) =
        vcat $ header "Search" :: map (indent 2)
          [ "depth:" <++> byShow depth
          , "in:" <++> pretty0 def ]
  prettyDef (Guess tm _ cs) =
        vcat $ header "Guess" :: map (indent 2)
          [ "solution:" <++> byShow tm
          , "when:" <++> byShow cs ]
  prettyDef (UniverseLevel i) = "Universe level #" <+> byShow i
  prettyDef ImpBind = "Bound name"
  prettyDef Delayed = "Delayed"

namespace Resugared
  export
  prettyTree : {vars : _} ->
    {auto c : Ref Ctxt Defs} ->
    {auto s : Ref Syn SyntaxInfo} ->
    Env Term vars -> Term vars -> Core (Doc IdrisSyntax)
  prettyAlt : {vars : _} ->
    {auto c : Ref Ctxt Defs} ->
    {auto s : Ref Syn SyntaxInfo} ->
    Env Term vars -> CaseAlt vars -> Core (Doc IdrisSyntax)

  export
  prettyDef : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Def -> Core (Doc IdrisDocAnn)
  prettyDef None = pure "undefined"
  prettyDef (Function _ ct _ pats) = do
      ct <- prettyTree (mkEnv emptyFC _) ct
      pure $ header "Compile time tree" <++> reAnnotate Syntax ct
  prettyDef (DCon nt tag arity) = pure $
      vcat $ header "Data constructor" :: map (indent 2)
          ([ "tag:" <++> byShow tag
           , "arity:" <++> byShow arity
           ] ++ maybe [] (\ n => ["newtype by:" <++> byShow n]) (newTypeArg nt))
  prettyDef (TCon ti arity) =
        let enum = hsep . punctuate ","
            ps = paramPos ti
            ms = mutWith ti
            det = detagBy ti
            cons = datacons ti in pure $
        vcat $ header "Type constructor" :: map (indent 2)
          ([ "arity:" <++> byShow arity
           , "parameter positions:" <++> byShow ps
           , "constructors:" <++> enum ((\ nm => annotate (Syntax $ DCon (Just nm)) (pretty0 nm)) <$> cons)
           ] ++ (("mutual with:" <++> enum (pretty0 <$> ms)) <$ guard (not $ null ms))
             ++ (maybe [] (\ pos => ["detaggable by:" <++> byShow pos]) det))
  prettyDef (ExternDef arity) = pure $
      vcat $ header "External definition" :: map (indent 2)
           [ "arity:" <++> byShow arity ]
  prettyDef (ForeignDef arity calls) = pure $
     vcat $ header "Foreign definition" :: map (indent 2)
          [ "arity:" <++> byShow arity
          , "bindings:" <++> byShow calls ]
  prettyDef (Hole numlocs hf) = pure $
        vcat $ header "Hole" :: map (indent 2)
          ("Implicitly bound name" <$ guard (implbind hf))
  prettyDef (BySearch rig depth def) = pure $
        vcat $ header "Search" :: map (indent 2)
          [ "depth:" <++> byShow depth
          , "in:" <++> pretty0 def ]
  prettyDef (Guess tm _ cs) = pure $
        vcat $ header "Guess" :: map (indent 2)
          [ "solution:" <++> byShow tm
          , "when:" <++> byShow cs ]
  prettyDef (UniverseLevel i) = pure $ "Universe level #" <+> byShow i
  prettyDef ImpBind = pure "Bound name"
  prettyDef Delayed = pure "Delayed"
