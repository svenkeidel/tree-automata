{-# LANGUAGE OverloadedStrings #-}
module TreeAutomata.Exp where

import           Control.Monad
import           Control.Monad.State

import           Data.IORef
import           Data.List hiding (union)
import qualified Data.Map as Map
import           Data.Text (Text)
import qualified Data.Text as Text

import           System.IO.Unsafe (unsafePerformIO)

import           TreeAutomata
import           Util (diagonalize')

import           TextShow

type NonTerm = Name

data Exp
  = Empty
  | Wild
  | Neg Exp
  | And Exp Exp
  | Or Text{-Ensures gensym-} Exp Exp
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
expToTA :: Alphabet -> Exp -> Grammar
expToTA ctxt = go where
  go Empty = empty
  go Wild = wildcard ctxt
  go (Neg e) = shrink $ dedup $ negateTA ctxt (shrink (dedup (go e)))
  go (And e1 e2) = error "expToTA.And: unimplemented"
  go (Or label e1 e2) = go e1 `union` go e2
  go (Cons c es) =
    if length es /= expected
    then error ("expToTA.Cons: "++show c++"("++show expected++"):" ++ show es)
    else Grammar start (Map.insert start [Ctor c starts] $
             foldr (Map.unionWith (++)) Map.empty prods) where
    expected = Map.findWithDefault (error "expToTA.Cons") c ctxt
    start = newU (Text.concat ["Cons(", showt c,")"])
    starts = [ s | Grammar s _ <- tas]
    prods = [ p | Grammar _ p <- tas]
    tas = map go es
  go (Hole nt) = Grammar start (Map.fromList [(start, [Eps nt])]) where
    start = newU (Text.concat ["Hole(", showt nt, ")"])
  go (Seq label e1 e2) = TreeAutomata.sequence label (go e1) (go e2)
  go (Star label e1) = Grammar start (Map.insert start [Eps label] $
                                 Map.insert label [Eps start1] prods1) where
    start = newU (Text.concat ["Star(", showt label, ")"])
    Grammar start1 prods1 = go e1
  go (Any nt) = go (AnyBut nt [])
  go (AnyBut nt ctors) = Grammar start (Map.union newProds prodsWild) where
    start = newU (Text.concat ["Any(", showt nt, ")"])
    Grammar startWild prodsWild = go Wild
    newProds =
      Map.insertWith (++) nt [] $
      Map.insertWith (++) start [Eps nt] $
      Map.fromList
      [(start,
         [Ctor c p
          | (c, i) <- Map.toList ctxt
          , i /= 0 -- Otherwise we might never go to start1
          , c `notElem` ctors
          , p <- diagonalize' id startWild (replicate i start)])]
  newU name = unsafePerformIO (newUnique  name)

type Neg a = State (Map.Map NonTerm [Rhs]) a
negateTA :: Alphabet -> Grammar -> Grammar
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
    let name = Text.append "neg:" (showt nts)
    done <- gets (Map.member name)
    unless done $ do
      modify (Map.insert name [])
      newProds <- Prelude.sequence [
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
  prods' = Prelude.sequence $ map (filter (not . isWild . snd)  . zip [0..]) prods
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
isWild nt =
  case Text.breakOnEnd ":" nt of
    (_, "Wild") -> True
    _ -> False

orExp :: Text -> [Exp] -> Exp
orExp s = go 0 where
  go :: Int -> [Exp] -> Exp
  go i [] = Empty
  go i [x] = x
  go i (x:xs) = Or (Text.append (showt i) s) x (go (i + 1) xs)


leftAssoc' :: Alphabet -> [Ctor] -> Grammar
leftAssoc' ctorInfo cs = expToTA ctorInfo (leftAssocExp ctorInfo cs)

leftAssocExp ctorInfo cs = exp where
  exp = Neg (Seq "s1" (Any "s1") (orExp "leftAssoc" violations))
  violations = [ Cons c1 (replicate (i1-1) Wild ++ [Cons c2 (replicate i2 Wild)]) |
                 c1 <- cs,
                 c2 <- cs,
                 let i1 = Map.findWithDefault (error "leftAssoc.c1") c1 ctorInfo,
                 let i2 = Map.findWithDefault (error "leftAssoc.c2") c2 ctorInfo]

rightAssoc' :: Alphabet -> [Ctor] -> Grammar
rightAssoc' ctorInfo cs = expToTA ctorInfo exp where
  exp = Neg (Seq "s1" (Any "s1") (orExp "rightAssoc" violations))
  violations = [ Cons c1 (Cons c2 (replicate i2 Wild) : replicate (i1-1) Wild) |
                 c1 <- cs,
                 c2 <- cs,
                 let i1 = Map.findWithDefault (error "rightAssoc.c1") c1 ctorInfo,
                 let i2 = Map.findWithDefault (error "rightAssoc.c2") c2 ctorInfo]

leftAssoc :: Alphabet -> [Ctor] -> Grammar
leftAssoc ctorInfo cs = Grammar ab (pAB +++ p +++ pABO) where
  Grammar ab pAB = anyButGrammar ctorInfo "Any" cs
  p = Map.fromList [("Any", [Ctor c (replicate (n-1) "Any" ++ [abo]) | (c, n) <- Map.assocs ctorInfo, c `elem` cs])]
  Grammar abo pABO = anyButOneGrammar ctorInfo "NoCtor" ab cs

rightAssoc :: Alphabet -> [Ctor] -> Grammar
rightAssoc ctorInfo cs = Grammar ab (pAB +++ p +++ pABO) where
  Grammar ab pAB = anyButGrammar ctorInfo "Any" cs
  p = Map.fromList [("Any", [Ctor c (abo : replicate (n-1) "Any") | (c, n) <- Map.assocs ctorInfo, c `elem` cs])]
  Grammar abo pABO = anyButOneGrammar ctorInfo "NoCtor" ab cs

assocs :: Alphabet -> [(Bool, [Ctor])] -> [Grammar]
assocs _ [] = []
assocs ctorInfo ((isLeft, ctors) : rest) = f ctorInfo ctors : assocs ctorInfo rest where
  f = if isLeft then leftAssoc else rightAssoc

assocs' :: Alphabet -> [(Bool, [Ctor])] -> [Grammar]
assocs' _ [] = []
assocs' ctorInfo ((isLeft, ctors) : rest) = f ctorInfo ctors : assocs ctorInfo rest where
  f = if isLeft then leftAssoc' else rightAssoc'

strictPrecidence ctorInfo css = {-normalize $-} epsilonClosure $ Grammar ab ({-pAB `unionProds`-} pAB' `unionProds` p) where
  name :: Int -> Text
  name i = Text.append "Prec" (showt i)
  --Grammar ab pAB = anyButGrammar ctorInfo "Any" (concat css)
  ab = name 1
  Grammar _ pAB' = anyButOneGrammar ctorInfo (name (length css + 1)) ab (concat css)
  p = (Map.fromList $ [(ab, [Eps (name 1)])]) `unionProds`
      (Map.fromList $ concat $ zipWith f [1..] css)
  f i cs =
    [(name i, Eps (name (i+1)) :
              [Ctor c (replicate n (name (i+1))) |
               (c, n) <- Map.assocs ctorInfo, c `elem` cs])]

precidence = precidenceGen f where
  f j c i = Just j

-- h returning Nothing means break out of the precidence hierarchy
-- h returning Just means go to that precidence level
precidenceGen :: (Int -> Ctor -> Arity -> Maybe Int) -> Alphabet -> [[Name]] -> Grammar
precidenceGen h ctorInfo css = {-normalize $-} epsilonClosure $ Grammar ab ({-pAB `unionProds`-} pAB' `unionProds` p) where
  name :: Int -> Text
  name i = Text.append "Prec" (showt i)
  --Grammar ab pAB = anyButGrammar ctorInfo "Any" (concat css)
  ab = name 1
  Grammar _ pAB' = anyButOneGrammar ctorInfo (name (length css + 1)) ab (concat css)
  p = (Map.fromList $ [(ab, [Eps (name 1)])]) `unionProds`
      (Map.fromList $ concat $ zipWith f [1..] css)
  f i cs =
    [(name i, Eps (name (i+1)) :
              [Ctor c [case h i c j of Nothing -> ab; Just k -> name k | j <- [0 .. n-1]] |
               (c, n) <- Map.assocs ctorInfo, c `elem` cs])]

anyButOneGrammar ctorInfo name alt ctors =
  Grammar name (Map.fromList [(name, [Ctor c (replicate n alt) | (c, n) <- Map.assocs ctorInfo, c `notElem` ctors])])

anyGrammar ctorInfo name = anyButGrammar ctorInfo name []

anyButGrammar ctorInfo name ctors = anyButOneGrammar ctorInfo name name ctors

uniqSource :: IORef Integer
uniqSource = unsafePerformIO (newIORef 0)
{-# NOINLINE uniqSource #-}

newUnique :: Text -> IO Text
newUnique s = do
  r <- atomicModifyIORef' uniqSource $ \x -> let z = x+1 in (z,z)
  return $ Text.concat ["uniq:", showt r, ":", s]
{-# NOINLINE newUnique #-}

(+++) :: Map.Map Name [Rhs] -> Map.Map Name [Rhs] -> Map.Map Name [Rhs]
p1 +++ p2 = Map.unionWith f p1 p2 where
  f x y = nub $ sort $ x ++ y

unionProds :: Map.Map Name [Rhs] -> Map.Map Name [Rhs] -> Map.Map Name [Rhs]
unionProds = (+++)
