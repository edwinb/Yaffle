module Core.Hash

-- This is so that we can store a hash of the interface in ttc files, to avoid
-- the need for reloading modules when no interfaces have changed in imports.
-- As you can probably tell, I know almost nothing about writing good hash
-- functions, so better implementations will be very welcome...

public export
interface Hashable a where
  hash : a -> Int
  hashWithSalt : Int -> a -> Int

  hash = hashWithSalt 5381
  hashWithSalt h i = h * 33 + hash i

infixl 5 `hashWithSalt`
