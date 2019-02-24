{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
module NonTerminal(NonTerminal(..)) where

import Control.Monad.State(State,get,put)

class NonTerminal n where
  type Gen n :: *
  fresh :: State (Gen n) n

instance NonTerminal Int where
  type Gen Int = Int
  fresh = do
    x <- get
    put (x+1)
    return x
