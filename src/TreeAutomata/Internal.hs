{-# LANGUAGE TupleSections, FlexibleContexts #-}
module TreeAutomata.Internal where

import           Control.DeepSeq
import           Control.Monad.Except
import           Control.Monad.State
import           Data.List
import           Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map
import           Data.IORef

import           System.IO.Unsafe (unsafePerformIO)

-- Data types for TreeAutomata
type Ctor = String -- Tree-constructor labels
type Name = String -- Non-terminal names
data Rhs = Ctor Ctor [Name] | Eps Name deriving (Show, Eq, Ord)
type Prod = (Name, Rhs)
-- TODO: rename Grammar to TreeAutomata
-- The second field of `Grammar` is strict so whnf is enough to get real benchmark numbers
data Grammar = Grammar Name !(Map.Map Name [Rhs]) deriving (Show, Eq, Ord)
type CtorInfo = Map.Map Ctor Arity
type Arity = Int
-- TODO: Naming context in grammar
instance NFData Grammar where
  rnf (Grammar s p) = rnf s `seq` rnf p
instance NFData Rhs where
  rnf (Ctor c ns) = rnf c `seq` rnf ns
  rnf (Eps n) = rnf n

pp :: Grammar -> String
pp (Grammar start prods) = "start: " ++ start ++ "\n" ++ concatMap f (sort $ Map.toList prods) where
  f (lhs, rhs) = unlines (map (g lhs) $ sort rhs)
  g lhs (Ctor c ns) = lhs ++ ":" ++ c ++ ": " ++ unwords ns
  g lhs (Eps n) = lhs ++ ": " ++ n


empty :: Grammar
empty = Grammar emptyStart (Map.fromList [(emptyStart, [])])

-- | Creates a grammar with all possible terms over a given signature
wildcard :: CtorInfo -> Grammar
wildcard ctxt = Grammar wildStart (Map.fromList [(wildStart, [Ctor c (replicate i wildStart) | (c, i) <- Map.toList ctxt])]) where

-- | Union of the languages of two grammars. The first string argument
-- becomes the new start symbol and should be unique.
union :: String -> Grammar -> Grammar -> Grammar
union start (Grammar start1 prods1) (Grammar start2 prods2) =
  Grammar start (Map.insert start [Eps start1, Eps start2] $
                   Map.unionWith (++) prods1 prods2)

-- | Test the equality of two regular tree grammars
eqGrammar :: Grammar -> Grammar -> Maybe [(Either String (), [(Name, Name)])]
eqGrammar g1 g2 = eqGrammar' (epsilonClosure g1) (epsilonClosure g2)

-- | Test equality without doing epsilon closure first
eqGrammar' :: Grammar -> Grammar -> Maybe [(Either String (), [(Name, Name)])]
eqGrammar' (Grammar s1 ps1) (Grammar s2 ps2) =
--  trace ("eqGrammar': " ++ s1 ++ " " ++ s2) $
  case [r | r@(Right _, _) <- rs] of
    [] -> Just rs
    _ -> Nothing
  where
  rs = runStateT (runExceptT (f s1 s2)) []
  f :: Name -> Name -> ExceptT String (StateT [(Name, Name)] []) ()
  f s1 s2 = do
    mapping <- get
    case lookup s1 mapping of
      Just s1' | s1' == s2 -> return ()
               | otherwise -> throwError $ "Name already assigned: " ++ show (s1, s1', s2)
      Nothing -> do {-trace ("putting: " ++ s1 ++ " -> " ++ s2) $-}
                    put ((s1, s2) : mapping)
                    let p1 = sort $ map (s1,) $ Map.findWithDefault (error "eqGrammar'.findWithDefault.p1") s1 ps1
                        p2 = sort $ map (s2,) $ Map.findWithDefault (error "eqGrammar'.findWithDefault.p2") s2 ps2
                    if length p1 /= length p2
                    then let p1ctors = [c | (_, Ctor c _) <- p1]
                             p2ctors = [c | (_, Ctor c _) <- p2]
                         in throwError $ "Different number of productions: " ++ intercalate " !!!!! " [s1, s2, show $ length p1, show $ length p2, show $ zip p1ctors p2ctors, show p1ctors, show p2ctors, unlines $ map show p1, unlines $ map show p2]
                    else do let p1' = [p | p@(_, Ctor _ _) <- p1] ++ [p | p@(_, Eps _) <- p1]
                            p2' <- lift $ lift $ map ([p | p@(_, Ctor _ _) <- p2]++) $ permutations [p | p@(_, Eps _) <- p2]
                            zipWithM_ g p1' p2'
  g :: Prod -> Prod -> ExceptT String (StateT [(Name, Name)] []) ()
  g (l1, Ctor c1 p1) (l2, Ctor c2 p2)
      | c1 /= c2 = throwError $ "Mismatched ctors: " ++ show (l1, Ctor c1 p1, l2, Ctor c2 p2)
      | otherwise = zipWithM_ f p1 p2
  g (l1, Eps n1) (l2, Eps n2) = f n1 n2
  g p1 p2 = throwError $ "Mismatched prods: " ++ show (p1, p2)

intersectGrammar :: Grammar -> Grammar -> Grammar
intersectGrammar (Grammar s1 p1) (Grammar s2 p2) = Grammar (intersectName s1 s2) (Map.fromList prods) where
  intersectName n1 n2 = "(" ++ n1 ++ "," ++ n2 ++ ")"
  prods = [(intersectName n1 n2,
            [Ctor c1 (zipWith intersectName x1 x2)
             | Ctor c1 x1 <- r1,
               Ctor c2 x2 <- r2,
               c1 == c2] ++
            [Eps (intersectName x n2) | Eps x <- r1] ++
            [Eps (intersectName n1 x) | Eps x <- r2])
           | (n1, r1) <- Map.toList p1,
             (n2, r2) <- Map.toList p2]

-- list the names that occur in a Rhs
rhsNames :: Rhs -> [Name]
rhsNames (Ctor _ ns) = ns
rhsNames (Eps n) = [n]

constructorInfo :: Grammar -> CtorInfo
constructorInfo (Grammar _ p) = r where
  r = case filter ((>1) . length) $ groupBy g $ ctors of
        [] -> Map.fromList ctors
        err -> error ("Inconsistent constructors: " ++ show err)
  ctors = nub $ sort $ concatMap f $ concat $ Map.elems p
  f (Ctor c n) = [(c, length n)]
  f (Eps _) = []
  g (c1, _) (c2, _) = c1 == c2

epsilonClosure :: Grammar -> Grammar
epsilonClosure (Grammar s p) = Grammar s (Map.mapWithKey (\k _ -> close k) p) where
  close name = [r | r@(Ctor _ _) <- concatMap (fromJust . flip Map.lookup p) reach {-(trace (show (name, reach)) reach)-}] where
    reach :: [Name]
    reach = Set.toList $ execState (epsReach name) Set.empty
  epsReach n = do r <- get
                  unless (Set.member n r) $ do
                    put (Set.insert n r)
                    sequence_ [epsReach k | Eps k <- Map.findWithDefault (error ("epsilonClosure.findWithDefault"++show(n))) n p]

{- Old method of complementing TA (never fully implemented)
----------------------------- NEW STUFF
complement :: Name -> [(Ctor, Int)] -> Grammar -> Grammar
complement any constructorInfo g = Grammar start prods' where
  (Grammar start prods) = g
  prods' = Map.fromList [(lhs, concat [comp lhs ctor | ctor <- constructorInfo])
                        | (lhs, _) <- Map.toList prods]
  comp lhs (ctor, ctorSize) =
    case getCtor lhs ctor of
      [] -> [Ctor ctor (replicate ctorSize any)]
      [rhs] -> [Ctor ctor ((replicate i any) ++ [rhs !! i] ++ (replicate (ctorSize - i - 1) any))
               | i <- [0 .. ctorSize - 1]]
      x -> error ("complement: too many ctor: " ++ show x)
  getCtor lhs ctor = [rhs | Ctor ctor' rhs <- case Map.lookup lhs prods of Just x -> x, ctor' == ctor]

complement' :: Name -> Grammar -> Grammar -> Grammar
complement' any (Grammar _ prods) g = complement any constructorInfo' g where
  constructorInfo' = nub $ sort $ [(c, length rhs)| (_, ps) <- Map.toList prods, (Ctor c rhs) <- ps]

--complementTest g = ??? where
--  Grammar "start" [("start", Ctor "PreIncrement" [any, any])]

{-
-- NOTE: assumes (1) no epsilons, (2) fixed arity labels, and (3) that tokens are identical for identical labels
determinize :: Grammar -> Grammar
determinize (Grammar s m) = result where
  -- First we group the productions by label
  --prodInits :: [(l, [(nt, [nt])])]
  --prodInits = mkProdInits (smapToList m)
  -- Next we loop until the qInit set stablizes
  loop :: Set (Set Name) -> [(Set Name, Rhs (Set Name) Ctor (Set Name))]
  loop qInit = if qInit == qInit' then prods' else loop qInit' where
    -- The next iteration of productions
    prods' :: [(Set Name, Rhs (Set Name) l (Set Name))]
    prods' = concatMap (uncurry rec0) prodInits
    -- The non-terminal names for that next iteration of productions
    qInit' :: Set (Set Name)
    qInit' = Set.fromList (map fst prods')
    -- The function that calculates the next iteration of productions for a given label (l)
    rec0 :: l -> [(nt, [nt])] -> [(Set Name, Rhs (Set Name) l (Set Name))]
    rec0 l prodInit = rec [] prodInit where
      -- Arguments:
      --   - Atoms already checked for this set of productions
      --   - The atoms left to be checked in a production along with the non-terminal for that production
      rec :: [Set Name] -> [(Name, [Name])] -> [(Set Name, Rhs (Set Name) l (Set Name))]
      rec qs [] = [] -- No productions match the selected qs
      rec qs prods
        -- end of label so return an answer
        | (_, []) <- head prods = [(Set.fromList (map fst prods), Seq l qs)]
        -- pick a set of q for the next atom and try each one that works
        | otherwise = concat [rec (qs ++ [q']) (filtermap (filterProd q') prods) | q' <- Set.toList qInit]
  -- The preductions for the new grammar
  finalProds :: [(Set Name, Rhs (Set Name) l (Set Name))]
  finalProds = loop Set.empty
  -- productions for the start non-terminal
  s' :: Set (Set Name)
  s' = Set.fromList [qs | (qs, rhs) <- finalProds, not (Set.null (s `Set.intersection` qs))]
  result = Grammar s' (smapFromList finalProds)
-}

-- Prods is a radix tree on the arguments to a constructor
data Prods = Prods
  [(Ctor, Name)] -- Given no more arguments, this is the constructors and the non-terminals to which they belong
  [(Name, Prods)] -- Given an additional argument, keep traversing down the tree with each Prods
  deriving (Ord, Eq, Show)

makeProds :: Map.Map Name [Rhs] -> Prods
makeProds m = go prods0 where
  prods0 :: [([Name], (Ctor, Name))]
  prods0 = [ (children, (c, n))
           | (n, rs) <- Map.toList m,
             Ctor c children <- rs]
  go :: [([Name], (Ctor, Name))] -> Prods
  go prods =
    Prods
    (concat [ctorAndName | Left ctorAndName <- fac])
    [(head, go rest) | Right (head, rest) <- fac] where
    fac = factorFstHead (sort prods)

factorFst :: (Ord (a, b), Eq a) => [(a, b)] -> [(a, [b])]
factorFst xs = map f (groupByFst xs) where
  f xs@(x : _) = (fst x, map snd xs)

groupByFst :: (Ord (a, b), Eq a) => [(a, b)] -> [[(a, b)]]
groupByFst = groupBy (\x y -> fst x == fst y) . sort

factorFstHead :: (Ord ([a], b), Eq a) => [([a], b)] -> [Either [b] (a, [([a], b)])]
factorFstHead xs =
  map f (groupByFstHead xs) where
  f xs@(([], _) : _) = Left (map snd xs)
  f xs@(x : _) = Right (head (fst x), map g xs)
  g (_ : a, b) = (a, b)

groupByFstHead :: (Ord ([a], b), Eq a) => [([a], b)] -> [[([a], b)]]
groupByFstHead = groupBy (\x y -> maybeHead (fst x) == maybeHead (fst y)) . sort

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(a, b) -> (a, f b))

maybeHead :: [a] -> Maybe a
maybeHead [] = Nothing
maybeHead (x : _) = Just x

determinize2 :: Grammar -> Grammar
determinize2 (Grammar s m) =
  loop [] where
  
  prods0 :: Prods
  prods0 = makeProds m
  loop :: [Set.Set Name] -> Grammar --[([Set.Set Name], [(Ctor, Set.Set Name)])]
  loop ss0 = if length ss0 == length ss1
             then Grammar s' (Map.fromList (startEdges ++ res3))
             else loop ss1 where

    res :: [([Set.Set Name], [(Ctor, Name)])]
    res = chooseS [] [prods0]

    res2 :: [([Set.Set Name], [(Ctor, Set.Set Name)])]
    res2 = mapSnd (mapSnd Set.fromList . factorFst) res

    newNt n = "{" ++ intercalate "," (sort $ Set.toList n) ++ "}"

    res3 :: [(Name, [Rhs])]
    res3 =
      factorFst
      [ (newNt nt, Ctor c (map newNt args)) | (args, cnts) <- res2, (c, nt) <- cnts]

    startEdges :: [(Name, [Rhs])]
    startEdges = [(s', [Eps (newNt n) | n <- ss0, s `elem` n])]

    s' = "det:start"

    ss1 = nub $ sort [s | (_, cn) <- res2, (_, s) <- cn]

    chooseS :: [Set.Set Name] -> [Prods] -> [([Set.Set Name], [(Ctor, Name)])]
    chooseS ss prods =
      (case self of (_, []) -> []; _ -> [self]) ++
      (case prods of [] -> []; _ -> r) where
      self :: ([Set.Set Name], [(Ctor, Name)])
      self = (ss, nub $ sort $ concat [c | Prods c _ <- prods])
      children :: [(Name, Prods)]
      children = concat [c | Prods _ c <- prods]
      r :: [([Set.Set Name], [(Ctor, Name)])]
      r = concat [chooseS (ss ++ [s]) (map snd (filter ((`elem` s) . fst) children)) | s <- ss0]

{-
  prods =
  [(ss, doneProds)]
  [filterProds prods s | s <- ??]
  chooseN c ns [] = prodInv (c, ns)
  chooseN c ns (s : ss) =
                    [chooseN | n <- s]
  
  for ctor:
    for s <- :
             for q <- s
             [<- matching]

             lookup

  
  for each constructor, find
  prodInv :: Map.Map (Ctor, [Name]) [Name]
  doProd :: [Name] -> [(Ctor, Name)] -> ??
  
  isValidProd :: [Name] -> [Set Name] -> ??
  isValidProd name []
    isValidProd' :: [Name] -> [(
-}

x = Grammar "X"
  (Map.fromList
   [("X", sort [
        Ctor "E" [],
        Ctor "A" ["X", "X"],
        Ctor "B" ["X", "X"],
        Ctor "C" ["Y", "X"]]),
    ("Y", sort [
        Ctor "E" [],
        Ctor "A" ["X", "X"],
        Ctor "C" ["Y", "X"]])])
-}

uniqSource :: IORef Integer
uniqSource = unsafePerformIO (newIORef 0)
{-# NOINLINE uniqSource #-}

newUnique :: String -> IO String
newUnique s = do
  r <- atomicModifyIORef' uniqSource $ \x -> let z = x+1 in (z,z)
  return ("uniq:"++show r++":"++s)
{-# NOINLINE newUnique #-}

emptyStart :: String
emptyStart = unsafePerformIO (newUnique "Empty")
{-# NOINLINE emptyStart #-}

wildStart :: String
wildStart = unsafePerformIO (newUnique "Wild")
{-# NOINLINE wildStart #-}

(+++) :: Map.Map Name [Rhs] -> Map.Map Name [Rhs] -> Map.Map Name [Rhs]
p1 +++ p2 = Map.unionWith f p1 p2 where
  f x y = nub $ sort $ x ++ y

unionProds :: Map.Map Name [Rhs] -> Map.Map Name [Rhs] -> Map.Map Name [Rhs]
unionProds = (+++)
