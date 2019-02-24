module Terminal where

import Control.Applicative
import Data.HashSet (HashSet)

class Foldable t => Terminal t where
  productive :: HashSet n -> t n -> Bool
  determinize :: Applicative m => (HashSet n -> m n') -> t n -> m (t n')
  subsetOf :: Alternative m => (HashSet n -> HashSet n' -> m ()) -> t n -> t n' -> m ()
