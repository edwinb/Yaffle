module Core.Core

import Data.List1
import Data.Vect

import public Data.IORef

import System.File

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
infixr 1 =<<
export %inline
(=<<) : (a -> CoreE err b) -> CoreE err a -> CoreE err b
(=<<) = flip (>>=)

-- Kleisli compose
infixr 1 >=>
export %inline
(>=>) : (a -> CoreE err b) -> (b -> CoreE err c) -> (a -> CoreE err c)
f >=> g = (g =<<) . f

-- Flipped kleisli compose
infixr 1 <=<
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

export %inline
whenJust : Maybe a -> (a -> CoreE err ()) -> CoreE err ()
whenJust (Just a) k = k a
whenJust Nothing k = pure ()

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

export
anyM : (a -> CoreE err Bool) -> List a -> CoreE err Bool
anyM f [] = pure False
anyM f (x :: xs)
    = if !(f x)
         then pure True
         else anyM f xs

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
