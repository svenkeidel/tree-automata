{-# LANGUAGE TupleSections, FlexibleContexts, OverloadedStrings #-}
module TreeAutomata
  ( Grammar(..)
  , Rhs (..)
  , Ctor
  , Name
  , CtorInfo
  , Arity
  , empty
  , wildcard
  , union
  , intersection
  , sequence
  , shrink
  , normalize
  , elimSingles
  , dedup
  , epsilonClosure
  ) where

import           Prelude hiding (sequence)
import           Control.DeepSeq
import           Control.Monad.Except hiding (sequence)
import           Control.Monad.State hiding (sequence)

import           Data.List hiding (union)
import qualified Data.Map as Map
import           Data.Maybe
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text

import           Debug.Trace

import           Util

-- Data types for TreeAutomata
type Ctor = Text -- Tree-constructor labels
type Name = Text -- Non-terminal names
data Rhs = Ctor Ctor [Name] | Eps Name deriving (Show, Eq, Ord)
type Prod = (Name, Rhs)
-- TODO: rename Grammar to TreeAutomata
-- The second field of `Grammar` is strict so whnf is enough to get real benchmark numbers
data Grammar = Grammar Name !(Map.Map Name [Rhs]) deriving (Ord)
type CtorInfo = Map.Map Ctor Arity
type Arity = Int

instance Show Grammar where
  show (Grammar start prods) = "start: " ++ Text.unpack start ++ "\n" ++ concatMap f (sort $ Map.toList prods)
    where
      f :: (Text, [Rhs]) -> String
      f (lhs, rhs) = unlines (map (g lhs) $ sort rhs)
      g :: Text -> Rhs -> String
      g lhs (Ctor c ns) = Text.unpack lhs ++ ":" ++ Text.unpack c ++ ": " ++ Text.unpack (Text.unwords ns)
      g lhs (Eps n) = Text.unpack lhs ++ ": " ++ Text.unpack n

instance Eq Grammar where
  g1 == g2 = isJust $ eqGrammar g1 g2

-- TODO: Naming context in grammar
instance NFData Grammar where
  rnf (Grammar s p) = rnf s `seq` rnf p
instance NFData Rhs where
  rnf (Ctor c ns) = rnf c `seq` rnf ns
  rnf (Eps n) = rnf n

-- | Empty regular tree grammar
empty :: Name -> Grammar
empty start = Grammar start (Map.fromList [(start, [])])

-- | Creates a grammar with all possible terms over a given signature
wildcard :: CtorInfo -> Name -> Grammar
wildcard ctxt start = Grammar start (Map.fromList [(start, [Ctor c (replicate i start) | (c, i) <- Map.toList ctxt])])

-- | Union of the languages of two grammars. The first string argument
-- becomes the new start symbol and should be unique.
union :: Text -> Grammar -> Grammar -> Grammar
union start (Grammar start1 prods1) (Grammar start2 prods2) =
  Grammar start (Map.insert start [Eps start1, Eps start2] $
                   Map.unionWith (++) prods1 prods2)

sequence :: Name -> Name -> Grammar -> Grammar -> Grammar
sequence start label (Grammar start1 prods1) (Grammar start2 prods2) =
  Grammar start (Map.insert start [Eps start1] $
                 Map.insertWith (++) label [Eps start2] $
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
                         in throwError $ "Different number of productions: " ++ intercalate " !!!!! " [show s1, show s2, show $ length p1, show $ length p2, show $ zip p1ctors p2ctors, show p1ctors, show p2ctors, unlines $ map show p1, unlines $ map show p2]
                    else do let p1' = [p | p@(_, Ctor _ _) <- p1] ++ [p | p@(_, Eps _) <- p1]
                            p2' <- lift $ lift $ map ([p | p@(_, Ctor _ _) <- p2]++) $ permutations [p | p@(_, Eps _) <- p2]
                            zipWithM_ g p1' p2'
  g :: Prod -> Prod -> ExceptT String (StateT [(Name, Name)] []) ()
  g (l1, Ctor c1 p1) (l2, Ctor c2 p2)
      | c1 /= c2 = throwError $ "Mismatched ctors: " ++ show (l1, Ctor c1 p1, l2, Ctor c2 p2)
      | otherwise = zipWithM_ f p1 p2
  g (l1, Eps n1) (l2, Eps n2) = f n1 n2
  g p1 p2 = throwError $ "Mismatched prods: " ++ show (p1, p2)

intersection :: Grammar -> Grammar -> Grammar
intersection (Grammar s1 p1) (Grammar s2 p2) = Grammar (intersectName s1 s2) (Map.fromList prods) where
  intersectName :: Text -> Text -> Text
  intersectName n1 n2 = Text.concat ["(", n1, ",", n2, ")"]
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
  close name = [r | r@(Ctor _ _) <- concatMap (fromJust . flip Map.lookup p) reach] where
    reach :: [Name]
    reach = Set.toList $ execState (epsReach name) Set.empty
  epsReach n = do
    r <- get
    unless (Set.member n r) $ do
      put (Set.insert n r)
      sequence_ [epsReach k | Eps k <- Map.findWithDefault (error ("epsilonClosure.findWithDefault"++show n)) n p]


introduceEpsilons :: Grammar -> Grammar
introduceEpsilons g = Grammar start $ Map.mapWithKey go prodMap where
  Grammar start prodMap  = shrink $ epsilonClosure g
  go :: Text -> [Rhs] -> [Rhs]
  go key prods =
    let isSubsetOf ps1 ps2 = Set.fromList ps1 `Set.isSubsetOf` Set.fromList ps2
        candidates = filter ((`isSubsetOf` prods) . snd) $ filter ((/= key) . fst) $ Map.toList prodMap
        best = last $ sortOn (length . snd) $ (key, []){-have at least one element for last-} : candidates
        ties = filter ((== length (snd best)) . length . snd) candidates
        ties' = sortOn (sum . map countEps . snd) ties
        countEps (Ctor _ []) = 1
        countEps _ = 0
        best' = head (ties' ++ [(key, [])]{-have at least one element for head-})
        msg = "!!! Warning: "++show (length ties)++"("++show (map (sum . map countEps . snd) ties')++") possibilities for '"++show key++"'\n" ++
              "!!! Need: " ++ show (Grammar key (Map.singleton key prods)) ++
              concat ["!!! Have: " ++ show (Grammar k (Map.singleton k p)) | (k, p) <- ties]
        warn = if length ties <= 1 then id else trace msg
    in if length (snd best') <= 1
       then prods
       else warn $ Eps (fst best') : go (Text.concat ["<", key, ">"]) (Set.toList $ Set.fromList prods `Set.difference` Set.fromList (snd best'))

substNames :: [[Name]] -> Grammar -> Grammar
substNames e g = foldr (subst . sort) g e where
  subst :: [Name] -> Grammar -> Grammar
  subst (n : ns) g = foldr (flip subst1 n) g ns

substNamesOrdered :: [[Name]] -> Grammar -> Grammar
substNamesOrdered e g = foldr subst g e where
  subst :: [Name] -> Grammar -> Grammar
  subst (n : ns) g = foldr (flip subst1 n) g ns

subst1 :: Name -> Name -> Grammar -> Grammar
subst1 n1 n2 (Grammar s p) = Grammar (substS n1 n2 s) (Map.fromList p') where
  p' = map h $ groupBy f $ sort $ concatMap (substP n1 n2) (Map.toList p)
  f (c1, _) (c2, _) = c1 == c2
  h (xs@((ctor,_):_)) = (ctor, filter (/= Eps ctor) $ nub $ sort $ concatMap snd xs)
substP n1 n2 (lhs, rhs) = [(substS n1 n2 lhs, nub $ sort $ map (substR n1 n2) rhs)]
substS n1 n2 s = if n1 == s then n2 else s
substR n1 n2 (Eps s) = Eps (substS n1 n2 s)
substR n1 n2 (Ctor c ns) = Ctor c (map (substS n1 n2) ns)

eqvClasses' :: Map.Map Int Name -> Map.Map Int [(Int, [Int])] -> Map.Map Int{-old name-} Int{-new name-}
eqvClasses' nameInv p = iter f init where
  ps@(p0 : _) = sort (Map.keys p)
  pList = Map.toList p
  init :: Map.Map Int Int
  initBasic = Map.fromList [(p, p0) | p <- ps]
  init = Map.fromList $ concatMap h $ Map.elems init1
  h ns@(n : _) = [(n', n) | n' <- ns]
  init0 :: Map.Map Int{-size-} [Int]
  init0 = Map.fromListWith (++) [(length rhs, [n]) | (n, rhs) <- Map.toList p]
  init1 :: Map.Map [Int]{-ctors-} [Int]
  init1 = Map.fromListWith (++) [(nub $ sort $ map fst rhs, [n]) | (n, rhs) <- Map.toList p]
  f :: Map.Map Int Int -> Map.Map Int Int -- name |-> repesentitive name
  f eqvs = {-trace ("eqvClasses':\n"++unlines [Map.findWithDefault (error "eqvClass'") i nameInv ++ " -> " ++ Map.findWithDefault (error "eqvClasses'") j nameInv | (i, j) <- Map.toList eqvs])-} result where
    inv :: Map.Map [(Int, [Int])] [Int{-old name-}] -- [(ctor, [nt])] |-> member names
    inv = foldr (uncurry (Map.insertWith (++)) . renameProds) Map.empty pList
    renameProds :: (Int, [(Int, [Int])]) -> ([(Int, [Int])], [Int])
    renameProds (n, rhs) = (map renameProd rhs, [n])
    renameProd (c, args) = (c, map renameName args)
    renameName i = Map.findWithDefault (error "eqvClasses'") i eqvs
    result :: Map.Map Int Int
    result = Map.fromList $ concatMap entries (Map.elems inv)
    entries [n] = [(n, n)]
    entries ns@(n : _) = [(n', n) | n' <- ns]

-- TODO: optimize shrink for two states and lots of prods since many TA are like that
-- | Optimizes a grammar by first calculating equivalence classes and then normalizing the grammar.
shrink :: Grammar -> Grammar
shrink g = normalize (eqvClasses {-elimSingleEps2-} g)

eqvClasses :: Grammar -> Grammar
eqvClasses (Grammar s p) = Grammar sFinal pFinal where
  Grammar sEps pEps = {-dedup $-} epsilonClosure (Grammar s p)

  names :: [Name]
  names = nub $ sort $ s : Map.keys p
  nameMap = Map.fromList (zip names [1..])
  nameInv = Map.fromList (zip [1..] names)

  ctors = nub $ sort $ concatMap f (concat (Map.elems pEps)) where
    f (Ctor c _) = [c]
    f _ = []
  ctorMap = Map.fromList (zip ctors [1..])

  mapName n = Map.findWithDefault (error "eqvClasses") n nameMap
  mapCtor c = Map.findWithDefault (error "eqvClasses") c ctorMap
  mapRhs (Ctor c args) = (mapCtor c, map mapName args)
  mapEntry (n, rhs) = (mapName n, map mapRhs rhs)

  p' :: Map.Map Int [(Int, [Int])]
  p' = {-trace ("\n\n\npEps:\n"++pp (Grammar sEps pEps)++"\n\n\n") $-} Map.fromList (map mapEntry (Map.toList pEps))

  renaming :: Map.Map Int{-old name-} Int{-new name-}
  renaming = eqvClasses' nameInv p'

  renamingInv :: Map.Map Int{-new name-} [Int]{-old name-}
  renamingInv = foldr (uncurry (Map.insertWith (++)) . (\(n,n') -> (n', [n]))) Map.empty (Map.toList renaming)

  renameName :: Name -> Name
  renameName n = {-trace ("renameName "++n++" -> "++n') $-} n' where
    n' =
      Map.findWithDefault (error "eqvClasses")
        (Map.findWithDefault (error "eqvClasses")
          (Map.findWithDefault (error "eqvClasses") n nameMap)
          renaming)
        nameInv
  renameRhs (Ctor c args) = Ctor c (map renameName args)
  renameRhs (Eps n) = Eps (renameName n)
  renameEntry :: (Int, [Int]) -> [(Name, [Rhs])]
  renameEntry (n, ns)
    | n /= Map.findWithDefault (error "eqvClasses") n renaming = []
    | otherwise = {-trace ("rhs':"++show rhs')-} [(n', rhs')] where
        n' = Map.findWithDefault (error "eqvClasses") n nameInv
        rhs' :: [Rhs]
        rhs' = filter (/= Eps n') $ nub $ sort $ map renameRhs $ concatMap prods ns'
        ns' :: [Name]
        ns' = map (\n' -> Map.findWithDefault (error "eqvClasses") n' nameInv) ns
        prods :: Name -> [Rhs]
        prods n' = Map.findWithDefault (error "eqvClasses") n' p
  sFinal = renameName s
--  pFinal = Map.fromList (concatMap renameEntry (Map.toList p))
  pFinal = Map.fromList (concatMap renameEntry (Map.toList renamingInv))

-- | Optimizes the grammar by:
-- 
--     * Eliminating non-terminals that have only a single epsilon transition
--     * Eliminating epsilon transitions to single constructor non-terminals
--     * Eliminating non-terminals that are used only once when that one time is an epsilon transition.
elimSingles = iter (elimSingleUse . elimSingleCtor . elimSingleEps)

-- TODO: build map, flatten map, apply to all prods
-- elimSingleEps2 :: Grammar -> Grammar
-- elimSingleEps2 (Grammar s p) = Grammar s' p' where
--   -- initial mappings from single epsilons
--   subst :: Map.Map Name Name
--   subst = Map.fromList [(n, n') | (n, [Eps n']) <- Map.toList p]
--   -- union find algorithm
--   flatten :: [Name] -> Map.Map Name Name -> Map.Map Name Name
--   flatten [] m = m
--   flatten (n : ns) m = flatten ns (flatten' n [] m) where
--     flatten' n ns m
--       | Just n' <- Map.lookup n m = flatten' n' (n:ns) m
--       | otherwise = foldr (\n' -> Map.insert n' n) m ns
--   -- transitive closure of subst
--   subst' :: Map.Map Name Name
--   subst' = flatten (Map.keys subst) subst
--   renameName n = Map.findWithDefault n n subst'
--   renameRhs (Ctor c args) = Ctor c (map renameName args)
--   renameRhs (Eps n) = Eps (renameName n)
--   s' = renameName s
--   p' = Map.fromList [(renameName n, map renameRhs rhs) |
--                       (n, rhs) <- Map.toList p,
--                       Map.notMember n subst' ]

-- | Eliminates non-terminals that have only a single epsilon transition
elimSingleEps :: Grammar -> Grammar
elimSingleEps (Grammar s p) =
  normalize (substNamesOrdered eqvs (Grammar s p))
  where
    eqvs = [[r, n] | (n, [Eps r]) <- Map.toList p]

-- | Eliminates epsilon transitions to single constructor non-terminals
elimSingleCtor :: Grammar -> Grammar
elimSingleCtor (Grammar s p) = normalize (Grammar s (Map.map (map f) p)) where
  f (Eps n) | [c] <- fromJust (Map.lookup n p) = c
  f c = c

-- | Eliminates non-terminals that are used only once when that one time is an epsilon transition
elimSingleUse (Grammar s p) = normalize (Grammar s (Map.map replaceSingleUse p)) where
  replaceSingleUse prods = concatMap replaceSingleUseProd prods
  replaceSingleUseProd (Eps n)
    | n `elem` singleUse = fromJust (Map.lookup n p)
  replaceSingleUseProd x = [x]
  singleUse = filter isSingleUse (Map.keys p)
  isSingleUse n = 1 == sum (map (useCount n) (Map.elems p))
  useCount n prods = sum (map (useCountProd n) prods)
  useCountProd n (Eps n')
    | n == n' = 1
    | otherwise = 0
  useCountProd n (Ctor _ rhs)
    | n `elem` rhs = 2 -- Use 2 since it can't be inlined
    | otherwise = 0

dedup :: Grammar -> Grammar
dedup (Grammar start prods) = Grammar start (Map.map (nub . sort) prods)

-- | Remove productions for empty non-terminals
dropEmpty :: Grammar -> Grammar
dropEmpty (Grammar s p) = Grammar s (Map.map filterProds (Map.filterWithKey (\k _ -> Set.member k nonEmpty) p)) where
  filterProds = filter (all (`Set.member` nonEmpty) . rhsNames)
  nonEmpty = execState (mapM_ f nulls) Set.empty
  invMap = Map.fromList $
           map (\xs -> (snd (head xs), nub $ sort $ map fst xs)) $
           groupBy (\a b -> snd a == snd b) $
           sortBy (\a b -> snd a `compare` snd b)
           [(l, x) | (l, r) <- Map.toList p, x <- concatMap rhsNames r]
  nulls = nub $ sort [l | (l, r) <- Map.toList p, Ctor _ [] <- r]
  f :: Name -> State (Set.Set Name) ()
  f n = do r <- get
           unless (Set.member n r) $ do
             when (any (all (`Set.member` r) . rhsNames) (case Map.lookup n p of Just x -> x)) $ do
               put (Set.insert n r)
               sequence_ [f x | x <- Map.findWithDefault [] n invMap]

-- Remove productions that are not reachable form the start
dropUnreachable :: Grammar -> Grammar
dropUnreachable (Grammar s p) = Grammar s (Map.filterWithKey (\k _ -> Set.member k reachables) p) where
  reachables = execState (f s) Set.empty
  f :: Name -> State (Set.Set Name) ()
  f n = do r <- get
           unless (Set.member n r) $ do
             put (Set.insert n r)
             sequence_ [mapM_ f (rhsNames x) | x <- fromMaybe (error ("error.dropUnreachable:"++show (n,s,p))) (Map.lookup n p)]

-- | Remove useless productions.
-- We drop unreachable first because that plays better with laziness.
-- But we also drop unreachable after droping empty, because the empty may lead to unreachable.
normalize :: Grammar -> Grammar
normalize = dropUnreachable . dropEmpty . dropUnreachable

intersectGrammar' :: Grammar -> Grammar -> Grammar
intersectGrammar' g1 g2 = normalize $ intersection g1 g2

-- | Add productions for all terminals named in the grammar (assumes terminal names start with '"')
addTerminals :: Grammar -> Grammar
addTerminals (Grammar start prods) = Grammar start (Map.fromList $ Map.toList prods ++ terminals) where
  terminals = nub $ sort
    [ (t, [Ctor t []]) | (_,  rhs) <- Map.toList prods, t <- concatMap rhsNames rhs, Text.head t == '"']

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
-}
