\begin{code}
{-# LANGUAGE RecordWildCards #-}
module Common
  ( Monoid(..)
  , fold
  , map
  ) where

-- | Laws:
--
--   * identity <> x = x
--   * x <> identity = x
--   * x <> (y <> z) = (x <> y) <> z
data Monoid a = Monoid
  { identity :: a
  , (<>)    :: a -> a -> a
  }

fold :: Monoid a -> [a] -> a
fold   Monoid{..} []       = identity
fold m@Monoid{..} (x : xs) = x <> fold m xs
\end{code}
