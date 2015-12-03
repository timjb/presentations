module BankersQueue where

import Data.List as L
import LenList as LL

data BQueue a =
  BQueue { heads :: LL.LenList a
         , tails :: LL.LenList a
         }

empty :: BQueue a
empty = BQueue mempty mempty

mappendReverse' :: [a] -> [a] -> [a]
mappendReverse' xs ys = go xs ys []
  where
    go [] [] rs = rs
    go (x:xs) (y:ys) rs = x : go xs ys (y:rs)

mappendReverse :: LenList a -> LenList a -> LenList a
mappendReverse (LenList n xs) (LenList m ys) = LenList (n+m) (mappendReverse' xs ys)

mkBQueue :: LenList a -> LenList a -> BQueue a
mkBQueue xs ys =
  if LL.length xs > LL.length ys
    then BQueue xs ys
    else BQueue (mappendReverse xs ys) mempty

uncons :: BQueue a -> Maybe (a, BQueue a)
uncons (BQueue xss ys) =
  case LL.uncons xss of
    Nothing -> Nothing
    Just (x, xs) -> Just (x, mkBQueue xs ys)

append :: BQueue a -> a -> BQueue a
append (BQueue xs ys) y = mkBQueue xs (cons y ys)
