{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
module NonTerm(NonTerm(..)) where

import Control.Monad.State(State,get,put)

class NonTerm n where
  type Gen n :: *
  fresh :: State (Gen n) n

instance NonTerm Int where
  type Gen Int = Int
  fresh = do
    x <- get
    put (x+1)
    return x
