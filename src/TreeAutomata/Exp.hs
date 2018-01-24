module TreeAutomata.Exp where

import Control.Monad
import Control.Monad.State
import Data.List hiding (union)
import System.IO.Unsafe (unsafePerformIO)

import qualified Data.Map as Map

import TreeAutomata.Internal
import TreeAutomata.Optimizations
import Util (diagonalize')

type NonTerm = Name

data Exp
  = Empty
  | Wild
  | Neg Exp
  | And Exp Exp
  | Or String{-Ensures gensym-} Exp Exp
  | Cons Ctor [Exp]
  | Hole NonTerm
  | Seq NonTerm Exp Exp
  | Star NonTerm Exp
  | Any NonTerm
  | AnyBut NonTerm [Ctor]
  | Left NonTerm
  | Right NonTerm
  deriving (Eq, Ord, Show)

-- TODO: Exp validator (e.g. check that holes are properly nested)
-- NOTE: start must not be hoisted up, otherwise the unsafeperformIO wont work
expToTA :: CtorInfo -> Exp -> Grammar
expToTA ctxt = go where
  go Empty = empty
  go Wild = wildcard ctxt
  go (Neg e) = shrink $ dedup $ negateTA ctxt (shrink (dedup (go e)))
  go (And e1 e2) = error "expToTA.And: unimplemented"
  go (Or label e1 e2) = union start (go e1) (go e2)
    where start = unsafePerformIO (newUnique ("Or("++show label++")"))
  go (Cons c es) =
    if length es /= expected
    then error ("expToTA.Cons: "++show c++"("++show expected++"):" ++ show es)
    else Grammar start (Map.insert start [Ctor c starts] $
             foldr (Map.unionWith (++)) Map.empty prods) where
    expected = Map.findWithDefault (error "expToTA.Cons") c ctxt
    start = unsafePerformIO (newUnique $ "Cons("++show c++")")
    starts = [ s | Grammar s _ <- tas]
    prods = [ p | Grammar _ p <- tas]
    tas = map go es
  go (Hole nt) = Grammar start (Map.fromList [(start, [Eps nt])]) where
    start = unsafePerformIO (newUnique $ "Hole("++show nt++")")
  go (Seq label e1 e2) = Grammar start (Map.insert start [Eps start1] $
                                Map.insertWith (++) label [Eps start2] $
                                Map.unionWith (++) prods1 prods2) where
    start = unsafePerformIO (newUnique $ "Seq("++show label++")")
    Grammar start1 prods1 = go e1
    Grammar start2 prods2 = go e2
  go (Star label e1) = Grammar start (Map.insert start [Eps label] $
                                 Map.insert label [Eps start1] $
                                  prods1) where
    start = unsafePerformIO (newUnique $ "Star("++show label++")")
    Grammar start1 prods1 = go e1
  go (Any nt) = go (AnyBut nt [])
  go (AnyBut nt ctors) = Grammar start (Map.union newProds prodsWild) where
    start = unsafePerformIO (newUnique $ "Any(" ++ show nt ++ ")")
    Grammar startWild prodsWild = go Wild
    newProds =
      Map.insertWith (++) nt [] $
      Map.insertWith (++) start [Eps nt] $
      Map.fromList $
      [(start,
         [Ctor c p
          | (c, i) <- Map.toList ctxt
          , i /= 0 -- Otherwise we might never go to start1
          , c `notElem` ctors
          , p <- diagonalize' id startWild (replicate i start)])]

type Neg a = State (Map.Map NonTerm [Rhs]) a
negateTA :: CtorInfo -> Grammar -> Grammar
--negateTA = error "negate"
negateTA ctxt (Grammar start prods) = evalState m Map.empty where
  -- TODO: "any" non-terminal
  -- TODO: "nothing" non-terminal
  Grammar startWild prodsWild = expToTA ctxt Wild
  m :: Neg Grammar
  m = do
    start' <- go [start]
    prods' <- get
    return $ Grammar start' (Map.union prodsWild prods')
  -- sort non-term names at start of `go`
  go :: [NonTerm] {- negate the union of these -} -> Neg NonTerm
  go [] = return startWild
  go nts0 = do
    let nts = nub (sort nts0)
    let name = "neg:"++show (sort nts)
    done <- gets (Map.member name)
    unless done $ do
      modify (Map.insert name [])
      newProds <- sequence [
        Ctor c <$> mapM go newProd
        | (c, i) <- Map.toList ctxt
        , newProd <- quux i (prodsForCtor i nts c) ]
      --trace ("\n\nnewProds:"++show (name,nts0,nts,newProds)) $ return ()
      modify (Map.adjust (newProds ++) name)
    return name
  prodsForCtor :: Int -> [NonTerm] -> Ctor -> [[NonTerm]]
  prodsForCtor i nts c = {-trace ("\n\nprodsForCtor:"++show(i,nts,c,r))-} r where
    r = nub (sort (concatMap (go . Eps) nts))
    go :: Rhs -> [[NonTerm]]
    go (Eps nt) =
      concatMap go $
      Map.findWithDefault (error "negateTA.prodsForCtor.go") nt prods
    go (Ctor c' args)
      | c' == c = [args]
      | otherwise = []


-- production(argument-position(non-terminal))
-- ->
-- production(argument-position(to-be-unioned(non-terminal)))
quux :: Int -> [[NonTerm]] -> [[[NonTerm]]]
quux i prods = r where
  prods' :: [[(Int, NonTerm)]]
  prods' = sequence $ map (filter (not . isWild . snd)  . zip [0..]) prods
  r = map (reconstruct i) prods'

reconstruct :: Int -> [(Int, NonTerm)] -> [[NonTerm]]
reconstruct 0 _ = []
reconstruct len list = map reverse $ go 0 [] $ sort list where
  go :: Int -> [NonTerm] -> [(Int, NonTerm)] -> [[NonTerm]]
  go i vs [] = vs : replicate (len - i - 1) []
  go i vs ((j, v) : xs)
    | i == j = go i (v : vs) xs
    | i < j  = vs : go (i + 1) [] ((j, v) : xs)
    | otherwise = error ("error: reconstruct.go: "++show (len,i,j,v,list))

isWild :: NonTerm -> Bool
isWild nt
  | Just nt' <- stripPrefix "uniq:" nt,
    Just i <- elemIndex ':' nt',
    drop (i + 1) nt' == "Wild" = True
  | otherwise = False

orExp :: String -> [Exp] -> Exp
orExp s = go 0 where
  go :: Int -> [Exp] -> Exp
  go i [] = Empty
  go i [x] = x
  go i (x:xs) = Or (s ++ show i) x (go (i + 1) xs)


