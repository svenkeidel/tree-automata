module TreeAutomata where
-- {-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- {-# LANGUAGE StandaloneDeriving #-}
-- {-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE OverloadedStrings #-}
-- {-# LANGUAGE TypeSynonymInstances #-}
-- module TreeAutomata
--   ( GrammarBuilder
--   , Grammar
--   , Rhs (..)
--   , NonTerm
--   , Alphabet
--   , Arity

--   -- Constructions
--   , singleton
--   , addConstructor
--   , wildcard
--   , union
--   -- , intersection

--   -- Transformations
--   , epsilonClosure
--   , dropUnreachable
--   , dropEmpty
--   , dropUnproductive
--   , normalize
--   , toSubterms
--   , fromSubterms
--   , determinize
--   , widen
--   , widen'
--   , replaceNonTerm
--   , replaceEdge
--   , wideningClashes
--   , correspondenceSet
--   , arcReplacements
--   , arcAncestor
--   , findAncestors
--   , wideMap

--   -- Queries
--   , produces
--   , subsetOf
--   , size
--   , height
--   , start
--   , productions
--   , alphabet

--   -- Predicates
--   , isEmpty
--   , isSingleton
--   , isProductive
--   , isDeterministic
--   ) where

-- import           Control.DeepSeq
-- import           Control.Monad.State

-- import           Data.Hashable
-- import           Data.List hiding (union)
-- import           Data.Map (Map)
-- import qualified Data.Map as Map
-- import           Data.Maybe
-- import           Data.HashSet (HashSet)
-- import qualified Data.HashSet as H
-- import           Data.Set (Set)
-- import qualified Data.Set as Set
-- import qualified Data.Text as Text
    
-- import           Text.Printf

-- import           NonTerm

-- data Rhs a = Ctor a [NonTerm] | Eps NonTerm deriving (Eq, Ord)

-- instance Show a => Show (Rhs a) where
--   show (Ctor c ns) = show c ++ "(" ++ Text.unpack (Text.intercalate ", " (map toText ns)) ++ ")"
--   show (Eps e) = show e

-- instance NFData a => NFData (Rhs a) where
--   rnf (Ctor c ns) = rnf c `seq` rnf ns
--   rnf (Eps n) = rnf n

-- -- The second field of `Grammar` is strict so whnf is enough to get real benchmark numbers
-- type ProdMap a = Map NonTerm [Rhs a]
-- data Grammar a = Grammar NonTerm !(ProdMap a)

-- instance (Ord a, Show a) => Show (Grammar a) where
--   show (Grammar s p) = "start: " ++ show s ++ "\n" ++ concatMap f (Map.toAscList p)
--     where
--       f :: (Ord a, Show a) => (NonTerm, [Rhs a]) -> String
--       f (lhs, rhs) = unlines (map (\rhs -> printf " → " (show lhs) (show rhs)) $ sort rhs)

-- -- TODO: Naming context in grammar
-- instance NFData a => NFData (Grammar a) where
--   rnf (Grammar s p) = rnf s `seq` rnf p

-- instance (Hashable a, Eq a) => Hashable (Grammar a) where
--   hashWithSalt s (Grammar _ ps) = hashWithSalt s (alph ps)
--     where
--       alph :: (Hashable a, Eq a) => ProdMap a -> HashSet a
--       alph m = H.fromList [ c | Ctor c _ <- concat $ Map.elems m]

-- type GrammarBuilder a = State Int (Grammar a)

-- instance (Ord a, Show a) => Show (GrammarBuilder a) where
--   show g = show (evalState g 0)

-- instance Ord a => Eq (GrammarBuilder a) where
--   g1 == g2 = d1 `subsetOf` d2 && d2 `subsetOf` d1 where
--     g1' = normalize (epsilonClosure g1)
--     g2' = normalize (epsilonClosure g2)
--     d1 = if isDeterministic g1' then g1' else determinize g1'
--     d2 = if isDeterministic g2' then g2' else determinize g2'

-- deriving instance NFData a => NFData (GrammarBuilder a)

-- instance (Hashable a, Eq a) => Hashable (GrammarBuilder a) where
--   hashWithSalt s g = hashWithSalt s (evalState g 0)

-- type Alphabet a = Map a [Arity]
-- type Arity = Int

-- -- | Creates a grammar with a single production from the start symbol
-- -- to the given constant. The resulting grammar is by definition
-- -- deterministic.
-- singleton :: a -> GrammarBuilder a
-- singleton c = do
--   s <- uniqueStart
--   return $ Grammar s (Map.singleton s [ Ctor c [] ])

-- -- | Create a grammar with the given start symbol and production
-- -- rules. Depending on the production map, the resulting grammar is
-- -- either deterministic or nondeterministic.
-- grammar :: NonTerm -> ProdMap a -> GrammarBuilder a
-- grammar s ps = return (Grammar s ps)

-- -- | Given a non-terminal symbol with n arguments, combines n grammars
-- -- into a single new grammar containing this constructor. If any of
-- -- the given grammars is nondeterministic, the resulting grammar is
-- -- also nondeterministic.
-- addConstructor :: Eq a => a -> [GrammarBuilder a] -> GrammarBuilder a
-- addConstructor n gs = do
--   s <- uniqueStart
--   gs' <- sequence gs
--   return $ Grammar s (Map.insertWith (++) s [ Ctor n (map start gs') ] (Map.unionsWith (\r1 r2 -> nub (r1 ++ r2)) (map productions gs')))

-- -- | Creates a grammar with all possible terms over a given
-- -- signature. This grammar is by definition nondeterministic.
-- wildcard :: Alphabet a -> GrammarBuilder a
-- wildcard ctxt = do
--   s <- uniqueStart
--   return $ Grammar s (Map.fromList [(s, [Ctor c (replicate i s) | (c, is) <- Map.toList ctxt, i <- is])])

-- -- | Union of two grammars. A new, unique start symbol is
-- -- automatically created.  If either of the grammars is empty, the
-- -- other is returned as-is. Deterministic grammars are not closed
-- -- under union, hence the resulting grammar may be nondeterministic.
-- union :: Eq a => GrammarBuilder a -> GrammarBuilder a -> GrammarBuilder a
-- union g1 g2
--  | isEmpty g1 = g2
--  | isEmpty g2 = g1
--  | otherwise = do
--      Grammar start1 prods1 <- g1
--      Grammar start2 prods2 <- g2
--      s <- uniqueStart
--      return $ Grammar s (Map.insert s (nub [Eps start1, Eps start2]) $ Map.unionWith (error "non terminals are not disjoint") prods1 prods2)

-- -- | Returns the intersection of the two given grammars.  The
-- -- intersection is taken by taking the cross products of 1) the
-- -- non-terminals, 2) the start symbols and 3) the production
-- -- rules. Intuitively, this runs both grammars in
-- -- parallel. Deterministic grammars are closed under intersection.
-- -- intersection :: Eq a => GrammarBuilder a -> GrammarBuilder a -> GrammarBuilder a
-- -- intersection g1 g2 = do
-- --   Grammar s1 p1 <- g1
-- --   Grammar s2 p2 <- g2
-- --   let
-- --     intersectNonTerm :: NonTerm -> NonTerm -> NonTerm
-- --     intersectNonTerm n1 n2 = Text.concat [n1, "⨯", n2]
-- --     prods = [(intersectNonTerm n1 n2, [Ctor c1 (zipWith intersectNonTerm x1 x2) | Ctor c1 x1 <- r1, Ctor c2 x2 <- r2, c1 == c2] ++
-- --                [Eps (intersectNonTerm x n2) | Eps x <- r1] ++ [Eps (intersectNonTerm n1 x) | Eps x <- r2])
-- --             | (n1, r1) <- Map.toList p1, (n2, r2) <- Map.toList p2]
-- --   normalize $ epsilonClosure $ return $ Grammar (intersectNonTerm s1 s2) (Map.fromList prods)

-- -- | Takes the epsilon closure of a grammar, preserving determinicity.
-- epsilonClosure :: GrammarBuilder a -> GrammarBuilder a
-- epsilonClosure g = do
--   Grammar s p <- g
--   let
--     -- Computes the set of non-terminals reachable via epsilon rules.
--     epsReach :: NonTerm -> Set NonTerm
--     epsReach name = go name Set.empty
--       where
--         go :: NonTerm -> Set NonTerm -> Set NonTerm
--         go n r 
--           | Set.member n r = r
--           | otherwise      = foldl' (\r' rhs -> case rhs of Eps k -> go k r'; _ -> r') r (p Map.! n)

--     close name = [ r | r@(Ctor _ _) <- concatMap (p Map.!) (epsReach name) ]

--   return $ Grammar s (Map.mapWithKey (\k _ -> close k) p)

-- -- | Removes productions that are not reachable form the start. This
-- -- may make a nondeterministic grammar deterministic, if the removed
-- -- productions are the only source of nondeterminism.
-- dropUnreachable :: GrammarBuilder a -> GrammarBuilder a
-- dropUnreachable g = do
--   Grammar s p <- g
--   let
--     reachables = execState (f s) Set.empty

--     f :: NonTerm -> State (Set NonTerm) ()
--     f n = do
--       r <- get
--       unless (Set.member n r) $ do
--         put (Set.insert n r)
--         sequence_ [mapM_ f (rhsNonTerms x) | x <- fromMaybe [] (Map.lookup n p)]

--   grammar s (Map.filterWithKey (\k _ -> Set.member k reachables) p)

-- -- | Removes productions for empty non-terminals
-- dropEmpty :: GrammarBuilder a -> GrammarBuilder a
-- dropEmpty g = do
--   -- TODO: this should be equivalent to dropUnproductive, but isn't. Why not?
--   Grammar s p <- g
--   let
--     filterProds = filter (all (`Set.member` nonEmpty) . rhsNonTerms)
--     nonEmpty = execState (mapM_ f nulls) Set.empty
--     invMap = invert (Map.map (concatMap rhsNonTerms) p)
--     nulls = Set.fromList [l | (l, r) <- Map.toList p, producesConstant r]
--     f :: NonTerm -> State (Set NonTerm) ()
--     f n = do r <- get
--              unless (Set.member n r) $
--                when (any (all (`Set.member` r) . rhsNonTerms) (p Map.! n)) $ do
--                  put (Set.insert n r)
--                  sequence_ [f x | x <- Map.findWithDefault [] n invMap]
--   grammar s (Map.map filterProds (Map.filterWithKey (\k _ -> Set.member k nonEmpty) p))

-- -- | Removes all nonproductive non-terminals from the given grammar. A
-- -- nonproductive non-terminal is a non-terminal that does not actually
-- -- produce a tree. This may make a nondeterministic grammar
-- -- deterministic, if the removed productions are the only source of
-- -- nondeterminism.
-- dropUnproductive :: GrammarBuilder a -> GrammarBuilder a
-- dropUnproductive g = do
--   Grammar start prods <- g
--   prodNs <- fmap productive g
--   let filterProds :: [Rhs a] -> [Rhs a]
--       filterProds = filter (all (`Set.member` prodNs) . rhsNonTerms)
--   grammar start (Map.map filterProds (Map.filterWithKey (\k _ -> k `Set.member` prodNs) prods))

-- -- | Removes useless productions. Unreachable productions are dropped
-- -- first because that plays better with laziness. But we also drop
-- -- unreachable after droping empty, because the empty may lead to
-- -- unreachable. This may make a nondeterministic grammar
-- -- deterministic, if the removed productions are the only source of
-- -- nondeterminism.
-- normalize :: GrammarBuilder a -> GrammarBuilder a
-- normalize = dropUnreachable . dropEmpty

-- -- | Destructs a grammar into a list of (c, [G]) tuples where c is a
-- -- constructor and [G] is a list of grammars, with each grammar G in
-- -- this tuple having as constructor a nonterminal from c as start symbol.
-- -- For example, for the start production S -> foo(A,B) | bar(C) this returns
-- -- [(foo,[G(A), G(B)]) ,(bar,[G(C)])]
-- toSubterms :: Ord a => GrammarBuilder a -> [(a,[GrammarBuilder a])]
-- toSubterms g =
--   let g' = epsilonClosure g
--       Grammar s ps = evalState g' 0
--   in [ (c,[determinize $ nthSubterm n m g' | (_,m) <- zip ts [0..]]) | (Ctor c ts,n) <- zip (fromMaybe [] (Map.lookup s ps)) [0..] ]

-- -- | The opposite of `toSubterms`, i.e., given such a list of tuples,
-- -- rebuilds the original grammar.
-- fromSubterms :: Eq a =>  [(a, [GrammarBuilder a])] -> GrammarBuilder a
-- fromSubterms [] = empty where
--   empty :: GrammarBuilder a
--   empty = do
--     start <- uniqueStart
--     grammar start (Map.singleton start [])
-- fromSubterms ((c,gs):xs) = foldr (\(c, gs) g -> union (addConstructor' c gs) g) (addConstructor' c gs) xs where
--   addConstructor' :: Eq a => a -> [GrammarBuilder a] -> GrammarBuilder a
--   addConstructor' c gs = addConstructor c gs

-- type RenameMap = Map ([NonTerm]) NonTerm

-- -- | Determinizes a nondeterministic grammar. If the given grammar is
-- -- already deterministic, the result is still deterministic.
-- determinize :: Ord a => GrammarBuilder a -> GrammarBuilder a
-- determinize g | isEmpty g = g
--               | otherwise = do
--   let Grammar s p = evalState (epsilonClosure g) 0
--   (ps,rmap) <- go [s] p Map.empty Map.empty
--   grammar (rmap Map.! [s]) ps
--  where
--    go :: Ord a => [NonTerm] -> ProdMap a -> ProdMap a -> RenameMap -> State Int (ProdMap a, RenameMap)
--    go ns p res rmap = case Map.lookup ns rmap of
--      Just n -> return (res,rmap)
--      Nothing -> do
--        n <- uniqueNt
--        let rmap' = Map.insert ns n rmap
--        -- N1  -> foo(A1 ,B1 ) | bar(B1)                               in G1
--        -- N1' -> foo(A1',B1') | biz(B1')                              in G1
--        -- N2  -> foo(A2, B2) | baz(B2)                                in G2
--        -- N1xN1'xN2 -> foo(A1xA1'xA2, B1xB1'xB2) | bar(B1) | bar(B2)  in G3
--        let prods = Map.fromListWith (++) $ map fromCtor $ concat $ map (p Map.!) ns
--        foldM (\(ps,rmap) (c,s) -> do
--                  -- Transpose reorders the subterms by columns so they can be
--                  -- merged. Look at the example of `foo`.
--                  -- transpose [ [A1,B1], [A1',B1'] ] == [ [A1,A1'], [B1,B1'] ]
--                  -- transpose [ [A2,B2]            ] == [ [A2]    , [B2]     ]
--                  let t = transpose s
--                  (ps',rmap') <- foldM (\(ps,rmap) ns -> go ns p ps rmap) (ps,rmap) t
--                  let subterms = map (rmap' Map.!) t
--                  return (Map.insertWith (\r1 r2 -> if head r1 `elem` r2 then r2 else r1 ++ r2) n [(Ctor c subterms)] ps',rmap')
--              ) (res,rmap') (Map.toList prods)
--    fromCtor :: Rhs a -> (a,[[NonTerm]])
--    fromCtor (Ctor c ns) = (c,[ns])
--    fromCtor _ = error "epsilon"

-- widen :: (Show a, Ord a) => GrammarBuilder a -> GrammarBuilder a -> GrammarBuilder a
-- widen g1 g2 = widen' g1 (union g1 g2)

-- type WideMap a = Map NonTerm (Int,Set a,[Rhs a])

-- widen' :: (Show a, Ord a) => GrammarBuilder a -> GrammarBuilder a -> GrammarBuilder a
-- widen' g1 g2 = do
--   let g1'@(Grammar s1 _) = evalState g1 0
--       g2'@(Grammar s2 _) = evalState g2 0
--       w1 = wideMap g1'
--       w2 = wideMap g2'
--       correspondence = correspondenceSet s1 w1 s2 w2
--       wideClashes = wideningClashes correspondence w1 w2
--       nodes = nodeReplacements g2' wideClashes w1 w2
--       arcs = arcReplacements g2' wideClashes w1 w2
--   if Map.null arcs
--     then if Map.null nodes
--       then g2
--       else
--         let ((n',a),_) = minimumBy (closestAncestor w2) (Map.toList nodes)
--         in normalize $ return $ replaceNonTerm n' a g2'
--     else
--       let ((n',a),edges) = minimumBy (closestAncestor w2) (Map.toList arcs)
--           (ctor,lhs,i) = Set.elemAt 0 edges
--       in normalize $ return $ replaceEdge ctor lhs i a g2'

-- -- | Heuristic: best node replacement is the one that has the closest ancestor.
-- closestAncestor :: WideMap a -> ((NonTerm,NonTerm),Set (a,NonTerm,Int)) -> ((NonTerm,NonTerm),Set (a,NonTerm,Int)) -> Ordering
-- closestAncestor w ((n,a),_) ((m,a'),_) = toEnum (d1 - d2) where
--   d1 = depth a w - depth n w
--   d2 = depth a' w - depth m w

-- -- | Replaces the given nonterminal throughout the entire grammar.
-- replaceNonTerm :: NonTerm -> NonTerm -> Grammar a -> Grammar a
-- replaceNonTerm n a (Grammar s ps) = if s == n then Grammar a ps' else Grammar s ps' where
--   ps' = Map.map (map (replace n a)) (Map.delete n ps)
--   replace n a rhs = case rhs of
--     Ctor c ts -> Ctor c (map (\m -> if m == n then a else m) ts)
--     Eps e     -> if e == n then Eps a else Eps e

-- -- | Replaces the ith nonterminal in constructor ctor in the right
-- -- hand side of the given lhs.  For example, A -> foo(B,C) | bar(B,C)
-- -- should become A -> foo(B',C) | bar(B,C) and A -> foo(B,B) should
-- -- become A -> foo(B',B).
-- replaceEdge :: (Show a, Eq a) => a -> NonTerm -> Int -> NonTerm -> Grammar a -> Grammar a
-- replaceEdge ctor lhs i ancestor (Grammar s ps) = Grammar s ps' where
--   ps' = Map.adjust (foldr (\rhs rhss -> case rhs of
--                               Ctor c' args | ctor == c' -> Ctor ctor (replace args i ancestor):rhss
--                               _ -> rhs:rhss) []) lhs ps

-- -- | Replaces the ith element in the given list with the given element.
-- -- TODO: make safe, or use Data.Seq.
-- replace :: [a] -> Int -> a -> [a]
-- replace xs i x = case splitAt i xs of
--   (front, element:back) -> front ++ x : back
--   _ -> xs

-- nodeReplacements :: Ord a => Grammar a -> Map (NonTerm,NonTerm) (Set (a,NonTerm,Int)) -> WideMap a -> WideMap a -> Map (NonTerm,NonTerm) (Set (a,NonTerm,Int))
-- nodeReplacements = findRule nodeAncestor

-- nodeAncestor :: Ord a => NonTerm -> NonTerm -> [NonTerm] -> WideMap a -> WideMap a -> Grammar a -> Maybe NonTerm
-- nodeAncestor _ _ [] _ _ _ = Nothing
-- nodeAncestor n n' ancs w1 w2 g = let
--   d2 = depth n' w2
--   -- Heuristic: the best ancestor is the one "closest" (depth-wise) to the current nonterminal n.
--   -- Based on nothing but gut feeling.
--   (_,a) = minimum $ map (\a -> (d2 - depth a w2,a)) ancs
--   -- Now test whether the found ancestor is a valid ancestor.
--   in if depth n w1 >= depth a w2 && not (overapproximates n' a (productions g)) && ((prlb' n' w2) `Set.isSubsetOf` (prlb' a w2)) || depth n w1 < depth n' w2
--      then Just a
--      else nodeAncestor n n' (delete a ancs) w1 w2 g

-- arcReplacements :: Ord a => Grammar a -> Map (NonTerm,NonTerm) (Set (a,NonTerm,Int)) -> WideMap a -> WideMap a -> Map (NonTerm,NonTerm) (Set (a,NonTerm,Int))
-- arcReplacements = findRule arcAncestor

-- arcAncestor :: Ord a => NonTerm -> NonTerm -> [NonTerm] -> WideMap a -> WideMap a -> Grammar a -> Maybe NonTerm
-- arcAncestor _ _ [] _ _ _ = Nothing
-- arcAncestor n n' ancs w1 w2 g = let
--   d2 = depth n' w2
--   -- Heuristic: the best ancestor is the one "closest" (depth-wise) to the current nonterminal n.
--   -- Based on nothing but gut feeling.
--   (_,a) = minimum $ map (\a -> (d2 - depth a w2,a)) ancs
--     -- Now test whether the found ancestor is a valid ancestor.
--     in if depth n w1 >= depth a w2 && overapproximates n' a (productions g)
--      then Just a
--      else arcAncestor n n' (delete a ancs) w1 w2 g

-- overapproximates :: Ord a => NonTerm -> NonTerm -> ProdMap a -> Bool
-- overapproximates n a ps = nontermGrammar `subsetOf` ancestorGrammar where
--   ancestorGrammar = grammar a ps
--   nontermGrammar = grammar n ps

-- wideningClash :: Ord a => NonTerm -> WideMap a -> NonTerm -> WideMap a -> Bool
-- wideningClash n w1 n' w2 = (depth n w1 == depth n' w2 && prlb' n w1 /= prlb' n' w2) || depth n w1 < depth n' w2

-- wideningClashes :: Ord a => Map (NonTerm,NonTerm) (Set (a,NonTerm,Int)) -> WideMap a -> WideMap a -> Map (NonTerm,NonTerm) (Set (a,NonTerm,Int))
-- wideningClashes correspondence w1 w2 = Map.filterWithKey (\(n,n') _ -> wideningClash n w1 n' w2) correspondence

-- -- | Given a set of widening topological clashes and a selection
-- -- function, findRule makes a selection from the clashes. See
-- -- arcReplacements and nodeReplacements.
-- findRule :: Ord a => (NonTerm -> NonTerm -> [NonTerm] -> WideMap a -> WideMap a -> Grammar a -> Maybe NonTerm)
--   -> Grammar a -> Map (NonTerm,NonTerm) (Set (a,NonTerm,Int)) -> WideMap a -> WideMap a -> Map (NonTerm,NonTerm) (Set (a,NonTerm,Int))
-- findRule selection g2 wideClashes w1 w2 = Map.foldrWithKey (\(n,n') edges ancestors -> case selection n n' (findAncestors n' w2 g2) w1 w2 g2 of
--     Nothing -> ancestors
--     Just a  -> Map.insert (n',a) edges ancestors) Map.empty wideClashes where

-- -- | Requires an epsilon closured grammar.
-- correspondenceSet :: Ord a => NonTerm -> WideMap a -> NonTerm -> WideMap a -> Map (NonTerm,NonTerm) (Set (a,NonTerm,Int))
-- correspondenceSet s1 w1 s2 w2 = go (Map.singleton (s1,s2) Set.empty) s1 s2 where
--   go correspondence n n' = if depth s1 w1 /= depth s2 w2 || prlb' s1 w1 /= prlb' s2 w2
--     then correspondence
--     else
--       -- TODO: this assumes the same order of right hand sides when zipping.
--       let toAdd = Map.fromListWith Set.union [ ((a,a'),Set.singleton (c,n',i)) | Ctor c args <- prods n w1, Ctor c' args' <- prods n' w2, c == c', (a,a',i) <- zip3 args args' [0..] ]
--       in Map.foldrWithKey (\(a,a') edges correspondence -> case Map.lookup (a,a') correspondence of
--            Nothing -> go (Map.insert (a,a') edges correspondence) a a'
--            Just edges' -> if edges `Set.isSubsetOf` edges'
--              then correspondence
--              else go (Map.insertWith Set.union (a,a') edges correspondence) a a') correspondence toAdd

-- -- | Finds all proper ancestors of a nonterminal, i.e., all
-- -- nonterminals that can (in)directly produce the given nonterminal not including
-- -- that nonterminal itself.
-- findAncestors :: NonTerm -> WideMap a -> Grammar a -> [NonTerm]
-- findAncestors n w g = Set.toList ancestors where
--   ancestors = go n w g $ Set.filter (\p -> p /= n && n `elem` children (prods p w)) (productive g)
--   go :: NonTerm -> WideMap a -> Grammar a -> Set NonTerm -> Set NonTerm
--   go n w g ancs = if ancs == ancs'' then ancs else go n w g ancs'' where
--     ancs' = Set.filter (\p -> not (Set.null (ancs `Set.intersection` Set.fromList (children (prods p w))))) (productive g)
--     ancs'' = Set.union ancs' ancs

-- depth :: NonTerm -> WideMap a -> Int
-- depth n w = let (d,_,_) = w Map.! n in d

-- prlb' :: NonTerm -> WideMap a -> Set a
-- prlb' n w = let (_,p,_) = w Map.! n in p

-- prods :: NonTerm -> WideMap a -> [Rhs a]
-- prods n w = let (_,_,p) = w Map.! n in p

-- -- | The principal label set of a given nonterminal symbol is the set
-- -- of constructor names that it can generate.
-- prlb :: Ord a => NonTerm -> ProdMap a -> Set a
-- prlb n prods = Set.fromList [ c | Ctor c _ <- prods Map.! n ]

-- -- | This function computes the information required to perform the
-- -- widening.  This information is, for each nonterminal symbol in the
-- -- grammar, its depth and its principal label set.  The depth of a
-- -- nonterminal is defined as the smallest number of steps that it
-- -- takes to reach this nonterminal, from the start symbol. Per
-- -- definition, the depth of the start symbol is 0.
-- wideMap :: Ord a => Grammar a -> WideMap a
-- wideMap (Grammar s ps) = go s (Map.singleton s (0, prlb s ps, ps Map.! s)) where
--   go n w = foldr (\c w -> let (d',_,_) = w Map.! n in case Map.lookup c w of
--     Just (d'',prlbs,rhs) -> if (d'+1) < d'' then go c (Map.insert c (d'+1,prlbs,rhs) w) else w
--     Nothing -> go c (Map.insert c (d'+1,prlb c ps, ps Map.! c) w)) w (children $ ps Map.! n)

-- -- | Returns true iff the given grammar can construct the given constant.
-- produces :: Ord a => GrammarBuilder a -> a -> Bool
-- produces g n = any (elem n) (Set.map (\p -> [ c | Ctor c [] <- prods Map.! p]) (productive (Grammar s prods))) where
--   Grammar s prods = evalState g 0

-- data Constraint = Constraint (NonTerm, NonTerm) | Trivial Bool deriving (Show)
-- type ConstraintSet = Map (NonTerm,NonTerm) [[Constraint]]

-- -- | Test whether the first grammar is a subset of the second,
-- -- i.e. whether L(g1) ⊆ L(g2). Both grammars need to be deterministic,
-- -- or the results might is not reliable.
-- subsetOf :: Eq a => GrammarBuilder a -> GrammarBuilder a -> Bool
-- g1 `subsetOf` g2 = solve (s1,s2) $ generate Map.empty (Set.singleton (s1,s2)) where
--   Grammar s1 p1 = evalState g1 0
--   Grammar s2 p2 = evalState g2 0
--   -- Solves the generated set of constraints.
--   solve :: (NonTerm, NonTerm) -> ConstraintSet -> Bool
--   solve pair constraints = case Map.lookup pair constraints of
--     Just deps -> all (any (\dep -> case dep of Trivial t -> t; Constraint p -> solve p constraints)) deps
--     Nothing -> True
--   -- Generate constraints of the form S ⊆ S' iff (A⊆A' ∨ A⊆B') ∧ (B⊆A' ∨ B⊆B') ∧ (True)
--   -- for two production rules S -> foo(A) | foo(B) | c and S' -> foo(A') | foo(B') | c. This constraint is stored in a
--   -- ConstraintSet with key (S,S') and value [[Constraint ("A","A'"),Constraint ("A","B'")],...]. False results are
--   -- skipped as an optimization.
--   generate :: ConstraintSet -> Set (NonTerm,NonTerm) -> ConstraintSet
--   generate constraints toTest = if Set.null toTest
--     then constraints
--     else let
--       (a1,a2) = Set.elemAt 0 toTest
--       toTest' = Set.deleteAt 0 toTest
--       dependencies = map (map (\c -> case c of
--                                   Trivial t -> Trivial t
--                                   Constraint pair -> if pair `elem` Map.keys constraints || pair == (a1,a2)
--                                     then Trivial True
--                                     else Constraint pair)) $ shareCtor a1 a2
--       -- Insert dependencies into the map, regardless of whether there are any. Empty dependencies
--       -- are taken care of properly by `solve`.
--       constraints' = Map.insert (a1,a2) dependencies constraints
--       -- Insert any untested pair (a,b) into toTest.
--       toTest'' = foldl (foldl (\toTest dep -> case dep of
--                            Constraint pair | pair `notElem` Map.keys constraints' -> Set.insert pair toTest
--                            _ -> toTest)) toTest' dependencies
--     in generate constraints' toTest''
--   -- Given two nonterminals, e.g. S -> foo(A) | foo(B) | c and S' -> foo(A') | foo(B') | c, this function pairs
--   -- all constructors creating constraints of the form [[A⊆A' ∨ A⊆B' ∨ False],[B⊆A' ∨ B⊆B' ∨ False],[False ∨ False ∨ True].
--   -- As an optimization, False results are skipped entirely, creating instead [[A⊆A' ∨ A⊆B'],[B⊆A' ∨ B⊆B'],[True]
--   shareCtor :: NonTerm -> NonTerm -> [[Constraint]]
--   shareCtor a1 a2 = [ [ r | r2 <- Map.findWithDefault [] a2 p2, r <- match r1 r2 ] | r1 <- Map.findWithDefault [] a1 p1 ]
--   -- Given two constructors, this function creates the actual constraints:
--   -- 1. If two constants are identical, i.e. c and c from the example above, this is trivially true.
--   -- 2. If two constructors `foo` are found of equal arity, the constraint is formed pair-wise of their subterms.
--   -- 3. If none of these cases apply, then this is trivially false. As an optimization, false results are not actually
--   --    inserted in the list but rather skipped entirely.
--   match :: Eq a => Rhs a -> Rhs a -> [Constraint]
--   match r1 r2 = case (r1, r2) of
--     (Ctor c []  , Ctor c' []   ) | c == c' -> [Trivial True]
--     (Ctor c args, Ctor c' args') | c == c' && eqLength args args' -> zipWith (\a1 a2 -> Constraint (a1,a2)) args args'
--     (Eps e      , Eps e'       ) -> [Constraint (e,e')]
--     _                            -> [Trivial False]

-- -- | The size of a regular tree grammar is defined as SUM_(A∈N)(SUM_(A→α) |Aα|).
-- size :: GrammarBuilder a -> Int
-- size g = Map.foldr (\rhss acc -> foldr (\rhs acc -> 1 + sizeRhs rhs + acc) acc rhss) 0 ps where
--   Grammar _ ps = evalState g 0

-- -- | The height of a regular tree grammar is defined as the number of production rules.
-- height :: GrammarBuilder a -> Int
-- height g = Map.foldr (\rhss acc -> acc + length rhss) 0 ps where
--   Grammar _ ps = evalState g 0

-- -- | Returns the start symbol of the given grammar.
-- start :: Grammar a -> NonTerm
-- start (Grammar s _) = s

-- -- | Returns the productions of the given grammar.
-- productions :: Grammar a -> ProdMap a
-- productions (Grammar _ ps) = ps

-- -- | Returns the alphabet over which the given grammar operates.
-- alphabet :: Ord a => GrammarBuilder a -> Alphabet a
-- alphabet g = Map.foldl go Map.empty p where
--   Grammar _ p = evalState g 0
--   go :: Ord a => Alphabet a -> [Rhs a] -> Alphabet a
--   go acc [] = acc
--   go acc (n:ns) = case n of
--     Ctor c n -> go (Map.insert c [length n] acc) ns
--     Eps _ -> go acc ns

-- -- | Test whether the given grammar generates the empty language.  In
-- -- regular tree automata, emptiness can be tested by computing whether
-- -- any reachable state is a finite state. In a regular tree grammar,
-- -- this comes down to computing whether the start symbol is
-- -- productive.
-- isEmpty :: GrammarBuilder a -> Bool
-- isEmpty g = not (isProductive s g') where
--   g' = evalState g 0
--   s = start g'

-- -- | Tests whether the given grammar produces a single term. This can
-- -- be tested by checking that every non-terminal symbol has no
-- -- alternative productions, and that the start symbol is productive.
-- -- Non-singletonness may hide in unproductive or unreachable production rules,
-- -- so make sure those are removed first.
-- isSingleton :: GrammarBuilder a -> Bool
-- isSingleton g = isProductive s (Grammar s ps) && noAlts where
--   Grammar s ps = evalState g 0
--   noAlts = all (\rhss -> length rhss <= 1) (Map.elems ps)

-- -- | Tests whether the given nonterminal is productive in the given
-- -- grammar.
-- isProductive :: NonTerm -> Grammar a -> Bool
-- isProductive n g = Set.member n (productive g)

-- -- | Checks if the given grammar is deterministic. A deterministic
-- -- grammar has no production rules of the form X -> foo(A) | foo(A').
-- -- Since nondeterminism may hide in unproductive or unreachable
-- -- production rules, make sure those are removed before calling this
-- -- function.
-- isDeterministic :: Eq a => GrammarBuilder a -> Bool
-- isDeterministic g = all (\rhss -> eqLength (nubBy determinicity rhss) rhss) (Map.elems m) where
--   Grammar _ m = evalState g 0
--   determinicity :: Eq a => Rhs a -> Rhs a -> Bool
--   determinicity (Ctor c args) (Ctor c' args') = c == c' && eqLength args args'
--   determinicity _ _ = False

-- -- | Returns all productive nonterminals in the given grammar.
-- productive :: Grammar a -> Set NonTerm
-- productive (Grammar _ prods) = execState (go prods) p
--   where

--     p = Set.fromList [ n | (n, rhss) <- Map.toList prods, producesConstant rhss]
  
--     go :: ProdMap a -> State (Set NonTerm) ()
--     go prods = do
--       p <- get
--       let p' = Set.union p $ Set.fromList [ n | (n, rhss) <- Map.toList prods, filter rhss p ]
--       put p'
--       if p == p' then return () else go prods

--     filter :: [Rhs a] -> Set NonTerm -> Bool
--     filter rhss p = case rhss of
--       (Ctor _ args : rhss) -> if and [ arg `Set.member` p | arg <- args] then True else filter rhss p
--       (Eps nonterm : rhss) -> if Set.member nonterm p then True else filter rhss p
--       [] -> False


-- -- | The size of a right hand side.
-- sizeRhs :: Rhs a -> Int
-- sizeRhs (Ctor _ args) = length args
-- sizeRhs (Eps _) = 1

-- -- | List the names that occur in a right hand side.
-- rhsNonTerms :: Rhs a -> [NonTerm]
-- rhsNonTerms (Ctor _ ns) = ns
-- rhsNonTerms (Eps n) = [n]

-- -- | List the names that occur in all right hand sides.
-- children :: [Rhs a] -> [NonTerm]
-- children = nub . concat . map rhsNonTerms

-- -- | Returns a grammar where the start symbol points to the m-th
-- -- subterm of the n-th production of the original start symbol.
-- -- If either index is out of bounds, the original grammar is returned.
-- nthSubterm :: Ord a => Int -> Int -> GrammarBuilder a -> GrammarBuilder a
-- nthSubterm n m g = do
--   Grammar s ps <- g
--   let prods = fromMaybe [] (Map.lookup s ps)
--   if n >= length prods
--     then g
--     else
--       let Ctor _ args = prods !! n
--       in if m >= length args
--            then g
--            else grammar (args !! m) ps

-- -- | Returns true iff any of the right hand sides in the given list
-- -- produces a constant.
-- producesConstant :: [Rhs a] -> Bool
-- producesConstant = isJust . find (\r -> case r of Ctor _ [] -> True; _ -> False)

-- eqLength :: [a] -> [b] -> Bool
-- eqLength [] [] = True
-- eqLength (_:as) (_:bs) = eqLength as bs
-- eqLength _ _ = False

-- -- | Inverts a map.
-- invert :: (Ord k, Ord v) => Map k [v] -> Map v [k]
-- invert m = Map.fromListWith (++) pairs
--     where pairs = [(v, [k]) | (k, vs) <- Map.toList m, v <- vs]

{-
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

substNamesOrdered :: [[Name]] -> Grammar -> Grammar
substNamesOrdered e g = foldr subst g e

subst :: [Name] -> Grammar -> Grammar
subst (n : ns) g = foldr (`subst1` n) g ns

subst1 :: Name -> Name -> Grammar -> Grammar
subst1 n1 n2 (Grammar s p) = Grammar (substS n1 n2 s) (Map.fromList p') where
  p' = map h $ groupBy f $ sort $ concatMap (substP n1 n2) (Map.toList p)
  f (c1, _) (c2, _) = c1 == c2
  h (xs@((ctor,_):_)) = (ctor, filter (/= Eps ctor) $ nub $ sort $ concatMap snd xs)
  substP n1 n2 (lhs, rhs) = [(substS n1 n2 lhs, nub $ sort $ map (substR n1 n2) rhs)]
  substS n1 n2 s = if n1 == s then n2 else s
  substR n1 n2 (Eps s) = Eps (substS n1 n2 s)
  substR n1 n2 (Ctor c ns) = Ctor c (map (substS n1 n2) ns)

eqvClasses' :: Map Int Name -> Map Int [(Int, [Int])] -> Map Int{-old name-} Int{-new name-}
eqvClasses' nameInv p = iter f init where
  ps@(p0 : _) = sort (Map.keys p)
  pList = Map.toList p
  init :: Map Int Int
  initBasic = Map.fromList [(p, p0) | p <- ps]
  init = Map.fromList $ concatMap h $ Map.elems init1
  h ns@(n : _) = [(n', n) | n' <- ns]
  init0 :: Map Int{-size-} [Int]
  init0 = Map.fromListWith (++) [(length rhs, [n]) | (n, rhs) <- Map.toList p]
  init1 :: Map [Int]{-ctors-} [Int]
  init1 = Map.fromListWith (++) [(nub $ sort $ map fst rhs, [n]) | (n, rhs) <- Map.toList p]
  f :: Map Int Int -> Map Int Int -- name |-> repesentitive name
  f eqvs = {-trace ("eqvClasses':\n"++unlines [Map.findWithDefault (error "eqvClass'") i nameInv ++ " -> " ++ Map.findWithDefault (error "eqvClasses'") j nameInv | (i, j) <- Map.toList eqvs])-} result where
    inv :: Map [(Int, [Int])] [Int{-old name-}] -- [(ctor, [nt])] |-> member names
    inv = foldr (uncurry (Map.insertWith (++)) . renameProds) Map.empty pList
    renameProds :: (Int, [(Int, [Int])]) -> ([(Int, [Int])], [Int])
    renameProds (n, rhs) = (map renameProd rhs, [n])
    renameProd (c, args) = (c, map renameName args)
    renameName i = Map.findWithDefault (error "eqvClasses'") i eqvs
    result :: Map Int Int
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

  p' :: Map Int [(Int, [Int])]
  p' = {-trace ("\n\n\npEps:\n"++pp (Grammar sEps pEps)++"\n\n\n") $-} Map.fromList (map mapEntry (Map.toList pEps))

  renaming :: Map Int{-old name-} Int{-new name-}
  renaming = eqvClasses' nameInv p'

  renamingInv :: Map Int{-new name-} [Int]{-old name-}
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
--   subst :: Map Name Name
--   subst = Map.fromList [(n, n') | (n, [Eps n']) <- Map.toList p]
--   -- union find algorithm
--   flatten :: [Name] -> Map Name Name -> Map Name Name
--   flatten [] m = m
--   flatten (n : ns) m = flatten ns (flatten' n [] m) where
--     flatten' n ns m
--       | Just n' <- Map.lookup n m = flatten' n' (n:ns) m
--       | otherwise = foldr (\n' -> Map.insert n' n) m ns
--   -- transitive closure of subst
--   subst' :: Map Name Name
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
-}
