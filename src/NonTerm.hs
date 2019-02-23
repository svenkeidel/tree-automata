{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module NonTerm(NonTerm,toText,nonTerm,uniqueStart,uniqueNt) where

import           Data.Hashable(Hashable)
import           Data.Text(Text)
import qualified Data.Text as T

import           Control.Monad.State(State,get,put)
import           Control.DeepSeq

newtype NonTerm = NonTerm Text deriving (Eq,Ord,NFData,Hashable)

toText :: NonTerm -> Text
toText (NonTerm tx) = tx

instance Show NonTerm where show (NonTerm x) = T.unpack x

nonTerm :: Text -> State Int NonTerm
nonTerm name = do
  x <- fresh
  return $ NonTerm $ name `T.append` (T.pack (show x))

uniqueStart :: State Int NonTerm
uniqueStart = nonTerm "Start"

uniqueNt :: State Int NonTerm
uniqueNt = nonTerm "Nt"

fresh :: State Int Int
fresh = do
  x <- get
  put (x+1)
  return x
