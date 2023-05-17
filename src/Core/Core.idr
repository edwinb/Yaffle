module Core.Core

import Core.TT

import Data.List1
import Data.Vect

import public Data.IORef

import System.File

import Libraries.Data.Tap
import Libraries.Data.IMaybe

-- CoreE is a wrapper around IO that is specialised for efficiency.
export
record CoreE err t where
  constructor MkCore
  runCore : IO (Either err t)

export
coreRun : CoreE err a ->
          (err -> IO b) -> (a -> IO b) -> IO b
coreRun (MkCore act) err ok
    = either err ok !act

export
coreFail : err -> CoreE err a
coreFail e = MkCore (pure (Left e))

export
wrapError : (err -> err) -> CoreE err a -> CoreE err a
wrapError fe (MkCore prog) = MkCore $ mapFst fe <$> prog

-- This would be better if we restrict it to a limited set of IO operations
export
%inline
coreLift : IO a -> CoreE err a
coreLift op = MkCore (do op' <- op
                         pure (Right op'))

{- Monad, Applicative, Traversable are specialised by hand for Core.

Ideally we won't need this forever, but until we can guarantee that this
implementation dictionaries are specialised away in Idris 2, we'll keep this.
-}

-- Functor (specialised)
export %inline
map : (a -> b) -> CoreE err a -> CoreE err b
map f (MkCore a) = MkCore (map (map f) a)

export %inline
(<$>) : (a -> b) -> CoreE err a -> CoreE err b
(<$>) f (MkCore a) = MkCore (map (map f) a)

export %inline
(<$) : b -> CoreE err a -> CoreE err b
(<$) = (<$>) . const

export %inline
ignore : CoreE err a -> CoreE err ()
ignore = map (\ _ => ())

-- This would be better if we restrict it to a limited set of IO operations
export
%inline
coreLift_ : IO a -> CoreE err ()
coreLift_ op = ignore (coreLift op)

-- Monad (specialised)
export %inline
(>>=) : CoreE err a -> (a -> CoreE err b) -> CoreE err b
(>>=) (MkCore act) f
    = MkCore (act >>=
                   \case
                     Left err => pure $ Left err
                     Right val => runCore $ f val)

export %inline
(>>) : CoreE err () -> CoreE err a -> CoreE err a
ma >> mb = ma >>= const mb

-- Flipped bind
export %inline
(=<<) : (a -> CoreE err b) -> CoreE err a -> CoreE err b
(=<<) = flip (>>=)

-- Kleisli compose
export %inline
(>=>) : (a -> CoreE err b) -> (b -> CoreE err c) -> (a -> CoreE err c)
f >=> g = (g =<<) . f

-- Flipped kleisli compose
export %inline
(<=<) : (b -> CoreE err c) -> (a -> CoreE err b) -> (a -> CoreE err c)
(<=<) = flip (>=>)

-- Applicative (specialised)
export %inline
pure : a -> CoreE err a
pure x = MkCore (pure (pure x))

export
(<*>) : CoreE err (a -> b) -> CoreE err a -> CoreE err b
(<*>) (MkCore f) (MkCore a) = MkCore [| f <*> a |]

export
(*>) : CoreE err a -> CoreE err b -> CoreE err b
(*>) (MkCore a) (MkCore b) = MkCore [| a *> b |]

export
(<*) : CoreE err a -> CoreE err b -> CoreE err a
(<*) (MkCore a) (MkCore b) = MkCore [| a <* b |]

export %inline
when : Bool -> Lazy (CoreE err ()) -> CoreE err ()
when True f = f
when False f = pure ()


export %inline
unless : Bool -> Lazy (CoreE err ()) -> CoreE err ()
unless = when . not

export
iwhen : (b : Bool) -> Lazy (CoreE err a) -> CoreE err (IMaybe b a)
iwhen True f = Just <$> f
iwhen False _ = pure Nothing

export
iunless : (b : Bool) -> Lazy (CoreE err a) -> CoreE err (IMaybe (not b) a)
iunless b f = iwhen (not b) f

export %inline
whenJust : Maybe a -> (a -> CoreE err ()) -> CoreE err ()
whenJust (Just a) k = k a
whenJust Nothing k = pure ()

export
iwhenJust : IMaybe b a -> (a -> CoreE err ()) -> CoreE err ()
iwhenJust (Just a) k = k a
iwhenJust Nothing k = pure ()

-- Control.Catchable in Idris 1, just copied here (but maybe no need for
-- it since we'll only have the one instance for Core Error...)
public export
interface Catchable m t | m where
    throw : {0 a : Type} -> t -> m a
    catch : m a -> (t -> m a) -> m a

    breakpoint : m a -> m (Either t a)

export
Catchable (CoreE err) err where
  catch (MkCore prog) h
      = MkCore ( do p' <- prog
                    case p' of
                         Left e => let MkCore he = h e in he
                         Right val => pure (Right val))
  breakpoint (MkCore prog) = MkCore (pure <$> prog)
  throw = coreFail

export
wrap : (e -> e') -> CoreE e a -> CoreE e' a
wrap f (MkCore prog)
    = MkCore (do p' <- prog
                 case p' of
                      Left e => pure (Left (f e))
                      Right val => pure (Right val))

-- Prelude.Monad.foldlM hand specialised for Core
export
foldlC : Foldable t => (a -> b -> CoreE err a) -> a -> t b -> CoreE err a
foldlC fm a0 = foldl (\ma,b => ma >>= flip fm b) (pure a0)

-- Traversable (specialised)
traverse' : (a -> CoreE err b) -> List a -> List b -> CoreE err (List b)
traverse' f [] acc = pure (reverse acc)
traverse' f (x :: xs) acc
    = traverse' f xs (!(f x) :: acc)

%inline
export
traverse : (a -> CoreE err b) -> List a -> CoreE err (List b)
traverse f xs = traverse' f xs []

export
mapMaybeM : (a -> CoreE err (Maybe b)) -> List a -> CoreE err (List b)
mapMaybeM f = go [<] where
  go : SnocList b -> List a -> CoreE err (List b)
  go acc [] = pure (acc <>> [])
  go acc (a::as) = do
    mb <- f a
    go (maybe id (flip (:<)) mb acc) as

%inline
export
for : List a -> (a -> CoreE err b) -> CoreE err (List b)
for = flip traverse

export
traverseList1 : (a -> CoreE err b) -> List1 a -> CoreE err (List1 b)
traverseList1 f xxs
    = let x = head xxs
          xs = tail xxs in
          [| f x ::: traverse f xs |]

export
traverseVect : (a -> CoreE err b) -> Vect n a -> CoreE err (Vect n b)
traverseVect f [] = pure []
traverseVect f (x :: xs) = [| f x :: traverseVect f xs |]

export
traverseSnocList : (a -> CoreE err b) -> SnocList a -> CoreE err (SnocList b)
traverseSnocList f [<] = pure [<]
traverseSnocList f (xs :< x) = [| traverseSnocList f xs :< f x |]

%inline
export
traverseOpt : (a -> CoreE err b) -> Maybe a -> CoreE err (Maybe b)
traverseOpt f Nothing = pure Nothing
traverseOpt f (Just x) = map Just (f x)

export
traversePair : (a -> CoreE err b) -> (w, a) -> CoreE err (w, b)
traversePair f (w, a) = (w,) <$> f a

export
traverse_ : (a -> CoreE err b) -> List a -> CoreE err ()
traverse_ f [] = pure ()
traverse_ f (x :: xs)
    = Core.do ignore (f x)
              traverse_ f xs
%inline
export
for_ : List a -> (a -> CoreE err ()) -> CoreE err ()
for_ = flip traverse_

%inline
export
sequence : List (CoreE err a) -> CoreE err (List a)
sequence (x :: xs)
   = do
        x' <- x
        xs' <- sequence xs
        pure (x' :: xs')
sequence [] = pure []

export
traverseList1_ : (a -> CoreE err b) -> List1 a -> CoreE err ()
traverseList1_ f xxs
    = do let x = head xxs
         let xs = tail xxs
         ignore (f x)
         traverse_ f xs

namespace PiInfo
  export
  traverse : (a -> CoreE err b) -> PiInfo a -> CoreE err (PiInfo b)
  traverse f Explicit = pure Explicit
  traverse f Implicit = pure Implicit
  traverse f AutoImplicit = pure AutoImplicit
  traverse f (DefImplicit t) = pure (DefImplicit !(f t))

namespace Binder
  export
  traverse : (a -> CoreE err b) -> Binder a -> CoreE err (Binder b)
  traverse f (Lam fc c p ty) = pure $ Lam fc c !(traverse f p) !(f ty)
  traverse f (Let fc c val ty) = pure $ Let fc c !(f val) !(f ty)
  traverse f (Pi fc c p ty) = pure $ Pi fc c !(traverse f p) !(f ty)
  traverse f (PVar fc c p ty) = pure $ PVar fc c !(traverse f p) !(f ty)
  traverse f (PLet fc c val ty) = pure $ PLet fc c !(f val) !(f ty)
  traverse f (PVTy fc c ty) = pure $ PVTy fc c !(f ty)

export
mapTermM : ({vars : _} -> Term vars -> CoreE err (Term vars)) ->
           ({vars : _} -> Term vars -> CoreE err (Term vars))
mapTermM f = goTerm where

    goTerm : {vars : _} -> Term vars -> CoreE err (Term vars)
    goTerm tm@(Local _ _ _) = f tm
    goTerm tm@(Ref _ _ _) = f tm
    goTerm (Meta fc n i args)
        = f =<< Meta fc n i <$> traverse (\ (c, t) => pure (c, !(goTerm t))) args
    goTerm (Bind fc x bd sc) = f =<< Bind fc x <$> traverse goTerm bd <*> goTerm sc
    goTerm (App fc fn c arg) = f =<< App fc <$> goTerm fn <*> pure c <*> goTerm arg
    goTerm (As fc u as pat) = f =<< As fc u <$> pure as <*> goTerm pat
    goTerm (Case fc t c sc sct alts)
        = f =<< Case fc t c <$> goTerm sc <*> goTerm sct <*> traverse goAlt alts
      where
        goForced : {vars : _} -> (Var vars, Term vars) ->
                   CoreE err (Var vars, Term vars)
        goForced (v, tm) = pure (v, !(goTerm tm))

        goScope : {vars : _} -> CaseScope vars -> CoreE err (CaseScope vars)
        goScope (RHS fs tm)
            = pure $ RHS !(traverse goForced fs) !(goTerm tm)
        goScope (Arg c x sc)
            = pure $ Arg c x !(goScope sc)

        goAlt : {vars : _} -> CaseAlt vars -> CoreE err (CaseAlt vars)
        goAlt (ConCase fc n t sc)
            = pure $ ConCase fc n t !(goScope sc)
        goAlt (DelayCase fc t a sc)
            = pure $ DelayCase fc t a !(goTerm sc)
        goAlt (ConstCase fc c tm)
            = pure $ ConstCase fc c !(goTerm tm)
        goAlt (DefaultCase fc tm)
            = pure $ DefaultCase fc !(goTerm tm)

    goTerm (TDelayed fc la d) = f =<< TDelayed fc la <$> goTerm d
    goTerm (TDelay fc la ty arg) = f =<< TDelay fc la <$> goTerm ty <*> goTerm arg
    goTerm (TForce fc la t) = f =<< TForce fc la <$> goTerm t
    goTerm tm@(PrimVal _ _) = f tm
    goTerm tm@(PrimOp fc op args)
        = f =<< PrimOp fc op <$> (traverseVect goTerm args)
    goTerm tm@(Erased _ _) = f tm
    goTerm tm@(Unmatched _ _) = f tm
    goTerm tm@(TType _ _) = f tm

export
anyM : (a -> CoreE err Bool) -> List a -> CoreE err Bool
anyM f [] = pure False
anyM f (x :: xs)
    = if !(f x)
         then pure True
         else anyM f xs

export
anyMSnoc : (a -> CoreE err Bool) -> SnocList a -> CoreE err Bool
anyMSnoc f [<] = pure False
anyMSnoc f (xs :< x)
    = if !(f x)
         then pure True
         else anyMSnoc f xs

-- TMP HACK since there's no Zippable instance for SnocList
export
zip : SnocList a -> SnocList b -> SnocList (a, b)
zip [<] sy = [<]
zip sx [<] = [<]
zip (sx :< x) (sy :< y) = zip sx sy :< (x, y)

export
allM : (a -> CoreE err Bool) -> List a -> CoreE err Bool
allM f [] = pure True
allM f (x :: xs)
    = if !(f x)
         then allM f xs
         else pure False

export
filterM : (a -> CoreE err Bool) -> List a -> CoreE err (List a)
filterM p [] = pure []
filterM p (x :: xs)
    = if !(p x)
         then do xs' <- filterM p xs
                 pure (x :: xs')
         else filterM p xs

public export
data Ref : (l : label) -> Type -> Type where
     [search l]
     MkRef : IORef a -> Ref x a

export
newRef : (x : label) -> t -> CoreE err (Ref x t)
newRef x val
    = do ref <- coreLift (newIORef val)
         pure (MkRef ref)

export %inline
get : (x : label) -> {auto ref : Ref x a} -> CoreE err a
get x {ref = MkRef io} = coreLift (readIORef io)

export %inline
put : (x : label) -> {auto ref : Ref x a} -> a -> CoreE err ()
put x {ref = MkRef io} val = coreLift (writeIORef io val)

export %inline
update : (x : label) -> {auto ref : Ref x a} -> (a -> a) -> CoreE err ()
update x f
  = do v <- get x
       put x (f v)

export
wrapRef : (x : label) -> {auto ref : Ref x a} ->
          (a -> CoreE err ()) ->
          CoreE err b ->
          CoreE err b
wrapRef x onClose op
  = do v <- get x
       o <- catch op $ \err =>
              do onClose v
                 put x v
                 throw err
       onClose v
       put x v
       pure o

export
cond : List (Lazy Bool, Lazy a) -> a -> a
cond [] def = def
cond ((x, y) :: xs) def = if x then y else cond xs def

export
condC : List (CoreE err Bool, CoreE err a) -> CoreE err a -> CoreE err a
condC [] def = def
condC ((x, y) :: xs) def
    = if !x then y else condC xs def

namespace Functor

  export
  [CORE] Functor (CoreE err) where
    map = Core.map

namespace Applicative

  export
  [CORE] Applicative (CoreE err) using Functor.CORE where
    pure = Core.pure
    (<*>) = Core.(<*>)

namespace Monad

  export
  [CORE] Monad (CoreE err) using Applicative.CORE where
    (>>=) = Core.(>>=)
    join mma = Core.(>>=) mma id
