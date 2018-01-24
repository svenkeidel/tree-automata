{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module TreeAutomata.Optimizations {-(
  introduceEpsilons,
  shrink,
  elimSingles,
  elimSingleEps',
  dropUnreachable,
  dropEmpty,
  intersectGrammar',
  normalize,
  dedup
  )-} where

import Control.Monad.Except
import Control.Monad.State
import Data.List
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map

import TreeAutomata.Internal
import Util (iter)

import Debug.Trace

{-
epsilonClose
shrink
sort by number of productions
independantly choose "best" from among smaller
-}

introduceEpsilons :: Grammar -> Grammar
introduceEpsilons g = Grammar start $ Map.mapWithKey go prodMap where
  Grammar start prodMap  = shrink $ epsilonClosure g
  go key prods =
    let isSubsetOf ps1 ps2 = Set.fromList ps1 `Set.isSubsetOf` Set.fromList ps2
        candidates = filter ((`isSubsetOf` prods) . snd) $ filter ((/= key) . fst) $ Map.toList prodMap
        best = last $ sortOn (length . snd) $ (key, []){-have at least one element for last-} : candidates
        ties = filter ((== length (snd best)) . length . snd) candidates
        ties' = sortOn (sum . map countEps . snd) ties
        countEps (Ctor _ []) = 1
        countEps _ = 0
        best' = head (ties' ++ [(key, [])]{-have at least one element for head-})
        msg = "!!! Warning: "++show (length ties)++"("++show (map (sum . map countEps . snd) ties')++") possibilities for '"++key++"'\n" ++
              "!!! Need: " ++ pp (Grammar key (Map.singleton key prods)) ++
              concat ["!!! Have: " ++ pp (Grammar k (Map.singleton k p)) | (k, p) <- ties]
        warn = if length ties <= 1 then id else trace msg
    in if length (snd best') <= 1
       then prods
       else warn $ Eps (fst best') : go ("<"++key++">") (Set.toList $ Set.fromList prods `Set.difference` Set.fromList (snd best'))

splitOffFirstGroup :: (a -> a -> Bool) -> [a] -> ([a],[a])
splitOffFirstGroup equal xs@(x:_) = partition (equal x) xs
splitOffFirstGroup _     []       = ([],[])

equivalenceClasses :: (a -> a -> Bool) -> [a] -> [[a]]
equivalenceClasses _     [] = []
equivalenceClasses equal xs = let (fg,rst) = splitOffFirstGroup equal xs
                              in fg : equivalenceClasses equal rst

equivalenceClasses' :: (Ord a) => (a -> a -> Bool) -> Set.Set a -> [Set.Set a]
equivalenceClasses' f = map Set.fromList . equivalenceClasses f . Set.toList

substNames :: [[Name]] -> Grammar -> Grammar
substNames e g = foldr subst g (map sort e) where
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

{-
eqvClasses :: Grammar -> [[Name]]
eqvClasses g = map (sort . Set.toList) $ iter f [Set.fromList $ Map.keys p] where
  Grammar s p = epsilonClosure g
  f :: [Set.Set Name] -> [Set.Set Name]
  f eqvs = concatMap (equivalenceClasses' nameEq') eqvs where
    nameEq' n1 n2 = eqProds (fromJust $ Map.lookup n1 p) (fromJust $ Map.lookup n2 p)
    eqProds ps1 ps2 = all (\p -> any (eqProd p) ps1) ps2 &&
                      all (\p -> any (eqProd p) ps2) ps1
    eqProd (Ctor c1 x1) (Ctor c2 x2) =
      c1 == c2 && length x1 == length x2 && and (zipWith nameEq x1 x2)
    nameEq n1 n2 = not (null [() | ns <- eqvs, n1 `Set.member` ns, n2 `Set.member` ns])
-}

{-
preEqvClasses :: Map.Map Name [Rhs] -> [[Name]]
preEqvClasses p = map (map fst) $ groupBy eq $ sortBy cmp ns where
  ns = [ (n, nub $ sort $ map ctor rhss) | (n, rhss) <- Map.toList p ]
  ctor (Ctor c _) = c
  eq (_, cs1) (_, cs2) = length cs1 == length cs2 && cs1 == cs2
  cmp :: (Name, [Ctor]) -> (Name, [Ctor]) -> Ordering
  cmp (_, cs1) (_, cs2) = case length cs1 `compare` length cs2 of
                            EQ -> cs1 `compare` cs2
                            o -> o
-}

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
    inv = foldr (uncurry (Map.insertWith (++))) Map.empty (map renameProds pList)
    renameProds :: (Int, [(Int, [Int])]) -> ([(Int, [Int])], [Int])
    renameProds (n, rhs) = (map renameProd rhs, [n])
    renameProd (c, args) = (c, map renameName args)
    renameName i = Map.findWithDefault (error "eqvClasses'") i eqvs
    result :: Map.Map Int Int
    result = Map.fromList $ concatMap entries (Map.elems inv)
    entries [n] = [(n, n)]
    entries ns@(n : _) = [(n', n) | n' <- ns]

-- TODO: optimize shrink for two states and lots of prods since many TA are like that
shrink g = normalize (eqvClasses2 ({-elimSingleEps2-} g))
--shrink' g = shrink_old g
--shrink = shrink'

{-

eqvClasses2 :: Grammar -> Grammar
eqvClasses2 (Grammar s p) = Grammar sFinal pFinal where
  Grammar sEps pEps = epsilonClosure (Grammar s p)

  names :: [Name]
  names = nub $ sort $ s : (Map.keys p)
  nameMap = Map.fromList (zip names [1..])
  nameInv = Map.fromList (zip [1..] names)

  ctors = nub $ sort $ concatMap f (concat (Map.elems pEps)) where
    f (Ctor c _) = [c]
    f _ = []
  ctorMap = Map.fromList (zip ctors [1..])
  ctorMap' x = Map.findWithDefault (error "eqvClasses") x ctorMap

  mapName n = Map.findWithDefault (error "eqvClasses") n nameMap
  mapCtor c = Map.findWithDefault (error "eqvClasses") c ctorMap
  mapRhs (Ctor c args) = (mapCtor c, map mapName args)
  mapEntry (n, rhs) = (mapName n, map mapRhs rhs)

  p' :: Map.Map Int [(Int, [Int])]
  p' = Map.fromList (map mapEntry (Map.toList pEps))

  renaming :: Map.Map Int{-old name-} Int{-new name-}
  renaming = eqvClasses' p'

  renamingInv :: Map.Map Int{-new name-} [Int]{-old name-}
  renamingInv = foldr (uncurry (Map.insertWith (++))) Map.empty (map (\(n,n') -> (n', [n])) (Map.toList renaming))

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
    | otherwise = [(n', filter (/= Eps n') $ map renameRhs rhs')] where
        n' = Map.findWithDefault (error "eqvClasses") n nameInv
        rhs' :: [Rhs]
        rhs' = nub $ sort $ concatMap prods ns'
        ns' :: [Name]
        ns' = map (\n' -> Map.findWithDefault (error "eqvClasses") n' nameInv) ns
        prods :: Name -> [Rhs]
        prods n' = Map.findWithDefault (error "eqvClasses") n' p
  sFinal = renameName s
--  pFinal = Map.fromList (concatMap renameEntry (Map.toList p))
  pFinal = Map.fromList (concatMap renameEntry (Map.toList renamingInv))
-}

eqvClasses2 :: Grammar -> Grammar
eqvClasses2 (Grammar s p) = Grammar sFinal pFinal where
  Grammar sEps pEps = {-dedup $-} epsilonClosure (Grammar s p)

  names :: [Name]
  names = nub $ sort $ s : (Map.keys p)
  nameMap = Map.fromList (zip names [1..])
  nameInv = Map.fromList (zip [1..] names)

  ctors = nub $ sort $ concatMap f (concat (Map.elems pEps)) where
    f (Ctor c _) = [c]
    f _ = []
  ctorMap = Map.fromList (zip ctors [1..])
  ctorMap' x = Map.findWithDefault (error "eqvClasses") x ctorMap

  mapName n = Map.findWithDefault (error "eqvClasses") n nameMap
  mapCtor c = Map.findWithDefault (error "eqvClasses") c ctorMap
  mapRhs (Ctor c args) = (mapCtor c, map mapName args)
  mapEntry (n, rhs) = (mapName n, map mapRhs rhs)

  p' :: Map.Map Int [(Int, [Int])]
  p' = {-trace ("\n\n\npEps:\n"++pp (Grammar sEps pEps)++"\n\n\n") $-} Map.fromList (map mapEntry (Map.toList pEps))

  renaming :: Map.Map Int{-old name-} Int{-new name-}
  renaming = eqvClasses' nameInv p'

  renamingInv :: Map.Map Int{-new name-} [Int]{-old name-}
  renamingInv = foldr (uncurry (Map.insertWith (++))) Map.empty (map (\(n,n') -> (n', [n])) (Map.toList renaming))

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

{-
eqvClasses :: Grammar -> Grammar
eqvClasses (Grammar s p) = Grammar s' p''' where
  ctors = nub $ sort $ map f (concat (Map.values p)) where
    f (Ctor c _) = c
  ctorMap = Map.fromList (zip ctors [1..])
  ctorMap' x = Map.findWithDefault (error "eqvClasses") x ctorMap
  ctorInv = Map.fromList (zip [1..] ctors)
  ctorInv' x = Map.findWithDefault (error "eqvClasses") x ctorInv
  rhsMap' (Cons 
  p' :: Map.Map Int [(Int, [Int])]
  p' = Map.fromtList [(nameMap' n, map rhsMap' rhs) | (n, rhs) <- Map.toList p]
  renaming = eqvClasses p'
  p'' = renaming
  p''' = namesInv
-}

{-
    result = foldr1 entry (Map.values inv)
    entry :: [Int] -> Map.Map Int Int -> Map.Map Int Int
    entry [n] p = Map.insert n n p
    entry ns p = entry' ns' n p where
      (n : ns') = sort ns
    entry' [] n p = p
    entry' (n' : ns) n p = entry' ns n (Map.insert n' n)
-}

{-
eqvClasses :: Grammar -> [[Name]]
eqvClasses g = map (sort . Set.toList) $ iter f $ map Set.fromList $ preEqvClasses p where
  Grammar s p = epsilonClosure g
  f :: [Set.Set Name] -> [Set.Set Name]
  f eqvs =
    {-trace ("eqvClasses:"++show (length eqvs)++" "++show (map Set.size eqvs)) $-}
      concatMap (equivalenceClasses'') eqvs where
--    equivalenceClasses'' :: Set.Set Name -> 
    equivalenceClasses'' = g where
      g s | Set.size s == 1 = [s]
          | otherwise = equivalenceClasses'  nameEq' s
    nameEq' n1 n2 = eqProds (fromJust $ Map.lookup n1 p) (fromJust $ Map.lookup n2 p)
    eqProds ps1 ps2 = length ps1 == length ps2 &&
                      all (\p -> any (eqProd p) ps1) ps2 &&
                      all (\p -> any (eqProd p) ps2) ps1
    eqProd (Ctor c1 x1) (Ctor c2 x2) =
      c1 == c2 && length x1 == length x2 && and (zipWith nameEq x1 x2)
    -- `Map.Map Name Name` maps all names to the same root
    eqvs' :: Map.Map Name Name
    eqvs' = Map.fromList [ (m, n) | eqv <- eqvs, let ns@(n:_) = Set.toList eqv, m <- ns ]
    nameEq n1 n2 =
      Map.findWithDefault (error "eqvClasses.nameEq.n1") n1 eqvs' ==
      Map.findWithDefault (error "eqvClasses.nameEq.n2") n2 eqvs'
--    nameEq n1 n2 = not (null [() | ns <- eqvs, n1 `Set.member` ns, n2 `Set.member` ns])
-}

{-
eqvClasses :: Grammar -> [[Name]]
eqvClasses g = map (sort . Set.toList) $ iter f [Set.fromList $ Map.keys p] where
  Grammar s p = epsilonClosure g
  f :: [Set.Set Name] -> [Set.Set Name]
  f eqvs =
    {-trace ("eqvClasses:"++show (length eqvs)++" "++show (map Set.size eqvs)) $ -}
      concatMap (equivalenceClasses' nameEq') eqvs where
    nameEq' n1 n2 = eqProds (fromJust $ Map.lookup n1 p) (fromJust $ Map.lookup n2 p)
    eqProds ps1 ps2 = length ps1 == length ps2 &&
                      all (\p -> any (eqProd p) ps1) ps2 &&
                      all (\p -> any (eqProd p) ps2) ps1
    eqProd (Ctor c1 x1) (Ctor c2 x2) =
      c1 == c2 && length x1 == length x2 && and (zipWith nameEq x1 x2)
    -- `Map.Map Name Name` maps all names to the same root
    eqvs' :: Map.Map Name Name
    eqvs' = Map.fromList [ (m, n) | eqv <- eqvs, let ns@(n:_) = Set.toList eqv, m <- ns ]
    nameEq n1 n2 =
      Map.findWithDefault (error "eqvClasses.nameEq.n1") n1 eqvs' ==
      Map.findWithDefault (error "eqvClasses.nameEq.n2") n2 eqvs'
--    nameEq n1 n2 = not (null [() | ns <- eqvs, n1 `Set.member` ns, n2 `Set.member` ns])
-}

{-
eqvClasses :: [Prod] -> [[Name]]
eqvClasses p = map (sort . Set.toList) $ iter f [Set.fromList $ nub $ sort $ map fst p] where
  Grammar _ p' = epsilonClosure (Grammar undefined p)
  f :: [Set.Set Name] -> [Set.Set Name]
  f eqvs = concatMap (map Set.fromList . equivalenceClasses nameEq' . Set.toList) eqvs where
    -- | Assumes n1 and n2 are from the same equivalence class
--    nameEq' n1 n2 = eqProds (getProdsEps n1 p) (getProdsEps n2 p)
    nameEq' n1 n2 = eqProds (map snd $ getProds n1 p') (map snd $ getProds n2 p')
    nameEq :: Name -> Name -> Bool
    nameEq n1 n2 = not (null [() | ns <- eqvs, n1 `Set.member` ns, n2 `Set.member` ns])
    eqProds ps1 ps2 = all (\p -> any (eqProd p) ps1) ps2 &&
                      all (\p -> any (eqProd p) ps2) ps1
--    eqProds p1 p2 = length p1 == length p2 &&
--                    and (zipWith eqProd (sort $ map snd p1) (sort $ map snd p2))
    -- ^ This assumes all lhs in p1 or p2 are same within themselves
    -- and that the arguments to the same constructor are always "similar"
    eqProd (Ctor c1 n1) (Ctor c2 n2) =
      c1 == c2 && length n1 == length n2 && and (zipWith nameEq n1 n2)
--    eqProd (Eps n1) (Eps n2) = True {- we don't care so we say true -}
--    eqProd _ _ = False
-}

--shrink_old g = normalize (substNames (eqvClasses g) g)

elimSingles = iter (elimSingleUse . elimSingleCtor . elimSingleEps)

-- TODO: build map, flatten map, apply to all prods
elimSingleEps2 :: Grammar -> Grammar
elimSingleEps2 (Grammar s p) = Grammar s' p' where
  -- initial mappings from single epsilons
  subst :: Map.Map Name Name
  subst = Map.fromList [(n, n') | (n, [Eps n']) <- Map.toList p]
  -- union find algorithm
  flatten :: [Name] -> Map.Map Name Name -> Map.Map Name Name
  flatten [] m = m
  flatten (n : ns) m = flatten ns (flatten' n [] m) where
    flatten' n ns m
      | Just n' <- Map.lookup n m = flatten' n' (n:ns) m
      | otherwise = foldr (\n' -> Map.insert n' n) m ns
  -- transitive closure of subst
  subst' :: Map.Map Name Name
  subst' = flatten (Map.keys subst) subst
  renameName n = Map.findWithDefault n n subst'
  renameRhs (Ctor c args) = Ctor c (map renameName args)
  renameRhs (Eps n) = Eps (renameName n)
  s' = renameName s
  p' = Map.fromList [(renameName n, map renameRhs rhs) |
                      (n, rhs) <- Map.toList p,
                      Map.notMember n subst' ]


-- Eliminates non-terminals that have only a single epsilon transition
elimSingleEps' = iter elimSingleEps

elimSingleEps (Grammar s p) = normalize (substNamesOrdered eqvs (Grammar s p)) where
  eqvs = [[r, n] | (n, [Eps r]) <- Map.toList p]

-- Eliminates epsilon transitions to single constructor non-terminals
elimSingleCtor (Grammar s p) = normalize (Grammar s (Map.map (map f) p)) where
  f (Eps n) | [c] <- fromJust (Map.lookup n p) = c
  f c = c

-- Eliminates non-terminals that are used only once when that one time is an epsilon transition
elimSingleUse (Grammar s p) = normalize (Grammar s (Map.map replaceSingleUse p)) where
  replaceSingleUse prods = concat (map replaceSingleUseProd prods)
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

-- Flattens epsilon transition from n to n'
flatten :: Name -> Name -> Grammar -> Grammar
flatten n n' (Grammar s p) = (Grammar s p') where
  p' = Map.insert n ps p
  ps = sort $ concatMap f (fromJust $ Map.lookup n p)
  f (Eps n'') | n'' == n' = fromJust $ Map.lookup n' p
  f c = [c]

dedup (Grammar start prods) = Grammar start (Map.map (nub . sort) prods)

-- Remove productions for empty non-terminals
dropEmpty (Grammar s p) = Grammar s (Map.map filterProds (Map.filterWithKey (\k _ -> Set.member k nonEmpty) p)) where
  filterProds = filter (all (`Set.member` nonEmpty) . rhsNames)
  nonEmpty = execState (mapM_ f nulls) Set.empty
  invMap = Map.fromList $
           map (\xs -> (snd (head xs), nub $ sort $ map fst xs)) $
           groupBy (\a b -> snd a == snd b) $
           sortBy (\a b -> snd a `compare` snd b) $
           [(l, x) | (l, r) <- Map.toList p, x <- concatMap rhsNames r]
  nulls = nub $ sort $ [l | (l, r) <- Map.toList p, Ctor _ [] <- r]
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
             sequence_ [mapM_ f (rhsNames x) | x <- case Map.lookup n p of Just y -> y; Nothing -> error ("error.dropUnreachable:"++show (n,s,p))]

-- Remove useless productions.
-- We drop unreachable first because that plays better with laziness.
-- But we also drop unreachable after droping empty, because the empty may lead to unreachable.
normalize :: Grammar -> Grammar
normalize = dropUnreachable . dropEmpty . dropUnreachable

intersectGrammar' :: Grammar -> Grammar -> Grammar
intersectGrammar' g1 g2 = normalize $ intersectGrammar g1 g2

shortNamesNames :: [String]
shortNamesNames = f ++ f' where
  f = map (:[]) $ ['A' .. 'Z'] ++ ['a' .. 'z']
  f' = (++) <$> shortNamesNames <*> f

shortNames :: Grammar -> Grammar
shortNames (Grammar s p) = Grammar s' p' where
  subst :: Map.Map String String
  subst = Map.fromList (zip (Map.keys p) shortNamesNames)
  renameName n = Map.findWithDefault (error "shortNames") n subst
  renameRhs (Ctor c ns) = Ctor c (map renameName ns)
  renameRhs (Eps n) = Eps (renameName n)
  s' = renameName s
  p' = Map.mapKeys renameName (Map.map (map renameRhs) p)
