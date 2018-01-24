module Util where

import Data.List (stripPrefix)
import Distribution.TestSuite (Test(..), TestInstance(..), Progress(..), Result(..))

-- iterate f on x until we reach a fixed point
iter :: (Eq a) => (a -> a) -> a -> a
iter f x = if x == x' then x else iter f x' where
  x' = f x

stripInfix :: (Eq a) => [a] -> [a] -> [a]
stripInfix s xs | Just xs <- stripPrefix s xs = stripInfix s xs
stripInfix s (x:xs) = x : stripInfix s xs
stripInfix s [] = []

progressFromMaybe Nothing = Finished Pass
progressFromMaybe (Just x) = Finished (Fail (show x))

simpleTest name run = Test $ TestInstance {
  run = progressFromMaybe <$> run,
  name = name,
  tags = [],
  options = [],
  setOption = \_ _ -> error $ "unimplemented setOption called on " ++ name
  }
