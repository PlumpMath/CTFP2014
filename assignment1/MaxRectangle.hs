-- |Max Rectangle
--
-- By Daniel O, Irene, Pablo, Fabian and Jeremy.
module MaxRectangle where

import Prelude hiding (Left, map)

class Binoid a where
  (+^) :: a -> a -> a
  (*^) :: a -> a -> a

  -- Satifsies
  -- (a +^ b) +^ c == a +^ (b +^ c)
  -- (a *^ b) *^ c == a *^ (b *^ c)

  -- Satisfies
  -- (a +^ b) *^ (c +^ d) == (a *^ c) +^ (b *^ d)

left, right :: a -> a -> a
left  a _ = a
right _ b = b

newtype Left a = Left { mkLeft :: a }

instance Binoid (Left a) where
  (+^) = left
  (*^) = left

dot :: Eq a => a -> a -> a
dot a b | a == b    = a
        | otherwise = undefined

data Array a
  = Singleton a
  | Above (Array a) (Array a)
  | Beside (Array a ) (Array a)
  deriving Show

(|||) :: Array a -> Array a -> Array a
(|||) = Beside

(|-|) :: Array a -> Array a -> Array a
(|-|) = Above

lift :: a -> Array a
lift a = Singleton a

height :: Array a -> Int
height (Singleton _) = 1
height (Above x y)   = height x + height y
height (Beside x y)  = height x `dot` height y

width :: Array a -> Int
width (Singleton _) = 1
width (Above x y)   = width x `dot` width y
width (Beside x y)  = width x + width y

ex :: Array Int
ex = (lift 1 |-| lift 3) ||| (lift 2 |-| lift 4) ||| (lift 5 |-| lift 6)

map :: (a -> b) -> Array a -> Array b
map f (Singleton a) = Singleton $ f a
map f (Above x y)   = map f x `Above` map f y
map f (Beside x y)  = map f x `Beside` map f y

reduce :: (a -> a -> a) -> (a -> a -> a) -> Array a -> a
reduce f g (Singleton a) = a
reduce f g (Above x y)   = reduce f g x `f` reduce f g y
reduce f g (Beside x y)  = reduce f g x `g` reduce f g y
