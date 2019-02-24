{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module TreeGrammar
( Grammar
, GrammarBuilder
, addConstructor
, union
, epsilonClosure
, dropUnreachable
, dropUnproductive
, productive
, determinize
, subsetOf
)
where

import           Prelude hiding (lookup)

import           Control.Arrow
import           Control.DeepSeq
import           Control.Monad.State

import           Data.Hashable
import qualified Data.List as L
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import           Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as Map
import           Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import           Data.Foldable

import           NonTerm


type Identifiable a = (Hashable a, Eq a)

data Grammar n t = Grammar { start :: n, productions :: ProdMap n t }
type ProdMap n t = HashMap n (Rhs n t)
data Rhs n t = Rhs { constrs :: Constructors n t, epsilons :: HashSet n }
newtype Constructors n t = Constructors (HashMap t (IntMap (HashSet [n])))

type GrammarBuilder n t = State (Gen n) (Grammar n t)

-- mapGrammar :: (Grammar n t -> Grammar n t') -> GrammarBuilder n t -> GrammarBuilder n t'
-- mapGrammar f = fmap f

cons :: (Identifiable n, Identifiable t) => t -> [n] -> Rhs n t
cons c ts =
  Rhs { constrs = Constructors
                $ Map.singleton c
                $ IM.singleton (length ts)
                $ Set.singleton ts
      , epsilons = mempty
      }

-- | @L(addConstructor c [g1...gn]) = [ c(t1...tn) | t1 in L(g1) ... tn in L(gn)]@
addConstructor :: (NonTerm n, Identifiable n, Identifiable t) => t -> [GrammarBuilder n t] -> GrammarBuilder n t
addConstructor n gs = do
  s <- fresh
  gs' <- sequence gs
  return $ Grammar s $ Map.insert s (cons n (start <$> gs'))
                     $ foldMap productions gs'

union :: (NonTerm n, Identifiable n, Identifiable t) => GrammarBuilder n t -> GrammarBuilder n t -> GrammarBuilder n t
union g1 g2 = do
  Grammar start1 prods1 <- g1
  Grammar start2 prods2 <- g2
  s <- fresh
  return $ Grammar s $ Map.insert s (mempty {epsilons = [start1, start2]})
                     $ Map.unionWith (error "non terminals are not disjoint") prods1 prods2

-- | Inlines all productions reachable via epsilon rules.
epsilonClosure :: (Identifiable n, Identifiable t) => Grammar n t -> Grammar n t
epsilonClosure g@(Grammar _ p) = g { productions = Map.mapWithKey close p } 
  where
    close name rhs =
      Rhs { constrs =
              constrs rhs <>
              constrs (foldMap (p Map.!) $ Set.toList (epsilonReachable name p))
          , epsilons = Set.empty
          }

-- Computes the set of non-terminals reachable via epsilon rules.
epsilonReachable :: forall n t. Identifiable n => n -> ProdMap n t -> HashSet n
epsilonReachable n0 p = go n0 Set.empty
  where
    go :: n -> HashSet n -> HashSet n
    go n r 
      | Set.member n r = r
      | otherwise      = foldl' (flip go) (Set.insert n r) (epsilons (p Map.! n))

lookup :: (Identifiable n, Identifiable t) => n -> ProdMap n t -> Constructors n t
lookup n p = constrs $ foldMap (p Map.!) $ Set.toList (epsilonReachable n p)

-- | Removes productions that are not reachable from the start symbol.
dropUnreachable :: (Identifiable n, Identifiable t) => Grammar n t -> Grammar n t
dropUnreachable g@(Grammar s p) =
  g { productions = Map.filterWithKey (\k _ -> Set.member k (reachable s g)) p }

reachable :: forall n t. (Identifiable n, Identifiable t) => n -> Grammar n t -> HashSet n
reachable n0 (Grammar _ p) = go n0 Set.empty
  where
    go :: n -> HashSet n -> HashSet n
    go n r
      | Set.member n r = r
      | otherwise      = foldl' (flip go) (Set.insert n r) (nonTerms (lookup n p))

dropUnproductive :: Identifiable n => Grammar n t -> Grammar n t
dropUnproductive g@(Grammar _ p) =
  g { productions = Map.filterWithKey (\k _ -> Set.member k (productive g)) p }

-- | Returns all productive nonterminals in the given grammar.
productive :: forall n t. Identifiable n => Grammar n t -> HashSet n
productive (Grammar _ prods) = go $ Set.fromList [ n | (n, rhs) <- Map.toList prods, producesConstant rhs]
  where
    producesConstant :: Rhs n t -> Bool
    producesConstant rhs = any (any null) (constructors' rhs)
  
    go :: HashSet n -> HashSet n
    go p =
      let p' = Set.union p $ Set.fromList [ n | (n, rhs) <- Map.toList prods, rhsProductive rhs p ]
      in if p == p' then p else go p'

    -- A right hand side is productive if one of its epsilon rules is
    -- productive or a all non-terminals of a constructor are productive.
    rhsProductive :: Rhs n t -> HashSet n -> Bool
    rhsProductive rhs prod = any (`Set.member` prod) (epsilons rhs)
                          || any (any (any (all (`Set.member` prod)))) (constructors' rhs)


type RenameMap n n' = HashMap (HashSet n) n'
determinize :: forall n n' t. (NonTerm n', Identifiable n, Identifiable n', Identifiable t) => Grammar n t -> GrammarBuilder n' t
determinize (Grammar s p) = state $ \i ->
  let (s',(i',(ps,_))) = runState (go [s]) (i,(mempty,mempty))
  in (Grammar s' ps, i')
 where
   -- go {N1,N2,N3}
   --    [ N1 -> foo(A1,B1) | bar(B1)
   --      N2 -> foo(A2,B2) | bar(B2)
   --      N3 -> foo(A3,B3) | baz(B3)
   --      ...
   --    ]
   -- = [ N1 U N2 U N3 -> foo(A1 U A2 U A3, B1 U B2 U B3) | bar(B1 U B2) | biz(B3) ... ]
   go :: HashSet n -> State (Gen n', (ProdMap n' t,RenameMap n n')) n'
   go ns = do
     rmap <- getRmap
     case Map.lookup ns rmap of
       Just x -> return x
       Nothing -> do
         n <- unique
         putRmap $ Map.insert ns n rmap
         let Constructors prods = foldMap (\k -> lookup k p) ns
         ctrs <- traverse (traverse (fmap Set.singleton . traverse go . transpose)) prods
         modifyRes $ Map.insert n (Rhs { constrs = Constructors ctrs, epsilons = mempty})
         return n

   unique :: State (Gen n',(ProdMap n' t,RenameMap n n')) n'
   unique = state (\(i,x) -> let (f,i') = runState fresh i in (f,(i',x)))

   getRmap :: State (Gen n',(ProdMap n' t',RenameMap n n')) (RenameMap n n')
   getRmap = snd . snd <$> get

   putRmap :: RenameMap n n' -> State (Gen n',(ProdMap n' t',RenameMap n n')) ()
   putRmap r = modify (second (second (const r)))

   modifyRes :: (ProdMap n' t -> ProdMap n' t) -> State (Gen n',(ProdMap n' t,RenameMap n n')) ()
   modifyRes f = modify (second (first f))

transpose :: Identifiable x => HashSet [x] -> [HashSet x]
transpose = fmap Set.fromList . L.transpose . Set.toList

-- | Test whether the first grammar is a subset of the second,
-- i.e. whether L(G1) ⊆ L(G2). The return value is either @Nothing@ or
-- a wittness of which non-terminals are a subset of other
-- non-terminals.  For example, if @([A,B],[X,Y]) in subsetOf G1 G2@ then
-- @L(G1(A)) U L(G1(B))  ⊆  L(G2(X)) U L(G2(Y))@.
subsetOf :: forall n1 n2 t. (Identifiable n1, Identifiable n2, Identifiable t)
         => Grammar n1 t -> Grammar n2 t -> Maybe [(HashSet n1,HashSet n2)]
Grammar s1 p1 `subsetOf` Grammar s2 p2 = fmap (fmap (\(x,y) -> (y,x)) . Map.toList) (execStateT (go [s1] [s2]) mempty)
  -- solve (s1,s2) $ generate Map.empty (Set.singleton (s1,s2))
  where
    go :: HashSet n1 -> HashSet n2 -> StateT (HashMap (HashSet n2) (HashSet n1)) Maybe ()
    go m1 m2 = do
      seen <- get
      let xs = Map.lookupDefault mempty m2 seen
      -- m1 ⊆ xs ⊆ m2
      unless (m1 `subset` xs) $ do
        put $ Map.insert m2 (xs `Set.union` m1) seen
        
        -- check if (m1-xs) ⊆ m2
        let m1' = m1 `Set.difference` xs
            Constructors c1 = foldMap (\k -> lookup k p1) m1'
            Constructors c2 = foldMap (\k -> lookup k p2) m2

        -- Check if the set of constructors of m1 is a subset of m2.
        guard $ Map.keysSet c1 `subset` Map.keysSet c2
        forM_ (Map.intersectionWith (,) c1 c2) $ \(a1,a2) -> do

          -- Check if the set of arities of m1 is a subset of m2.
          guard $ Set.fromList (IM.keys a1) `subset` Set.fromList (IM.keys a2)
          forM_ (IM.intersectionWith (,) a1 a2) $ \(l1,l2) ->
            zipWithM go (transpose l1) (transpose l2)

    subset :: Identifiable a => HashSet a -> HashSet a -> Bool
    subset m1 m2 = all (`Set.member` m2) m1

class Identifiable n => NonTerminals a n where
  nonTerms :: a -> HashSet n

instance Identifiable n => NonTerminals [n] n where
  nonTerms = Set.fromList

instance Identifiable n => NonTerminals (Grammar n t) n where
  nonTerms (Grammar _ p) = Set.fromList $ Map.keys p

instance Identifiable n => NonTerminals (Rhs n t) n where
  nonTerms rhs = nonTerms (constrs rhs) <> epsilons rhs

instance (Identifiable n, NonTerminals x n) => NonTerminals (HashSet x) n where
  nonTerms rhs = foldMap nonTerms rhs

instance NonTerminals x n => NonTerminals (HashMap a x) n where
  nonTerms m = foldMap nonTerms (Map.elems m)

instance NonTerminals x n => NonTerminals (IntMap x) n where
  nonTerms m = foldMap nonTerms (IM.elems m)

instance Identifiable n => NonTerminals (Constructors n t) n where
  nonTerms (Constructors m) = nonTerms m

instance (Identifiable n, Identifiable t) => Semigroup (Constructors n t) where
  Constructors c1 <> Constructors c2 = Constructors (Map.unionWith (IM.unionWith (<>)) c1 c2)
instance (Identifiable n, Identifiable t) => Monoid (Constructors n t) where
  mappend = (<>)
  mempty = Constructors Map.empty

instance (Identifiable n, Identifiable t) => Semigroup (Rhs n t) where
  Rhs c1 e1 <> Rhs c2 e2 = Rhs (c1 <> c2) (e1 <> e2)
instance (Identifiable n, Identifiable t) => Monoid (Rhs n t) where
  mappend = (<>)
  mempty = Rhs { constrs = mempty, epsilons = mempty }

constructors' :: Rhs n t -> HashMap t (IntMap (HashSet [n]))
constructors' (Rhs {constrs = Constructors c}) = c
