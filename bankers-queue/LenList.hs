module LenList where

import Prelude hiding (reverse)
import qualified Data.List as L

data LenList a = LenList { length :: !Int, items :: [a] }

instance Monoid (LenList a) where
  mempty = LenList 0 []
  mappend (LenList n xs) (LenList m ys) =
    LenList (n+m) (xs++ys)

uncons :: LenList a -> Maybe (a, LenList a)
uncons (LenList _ []) = Nothing
uncons (LenList n (x:xs)) = Just (x, LenList (n-1) xs)

cons :: a -> LenList a -> LenList a
cons x (LenList n xs) = LenList (succ n) (x : xs)

reverse :: LenList a -> LenList a
reverse (LenList n xs) = LenList n (L.reverse xs)