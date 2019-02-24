{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
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

import           NonTerminal
import           Terminal (Terminal)
import qualified Terminal as T


type Identifiable a = (Hashable a, Eq a)

data Grammar n t = Grammar { start :: n, productions :: ProdMap n t }
type ProdMap n t = HashMap n (Rhs n t)
data Rhs n t = Rhs { cons :: t n, eps :: HashSet n }
type GrammarBuilder n t = State (Gen n) (Grammar n t)
type IsGrammar n t = (Terminal t, Monoid (t n), NonTerminal n, Identifiable n)

-- mapGrammar :: (Grammar n t -> Grammar n t') -> GrammarBuilder n t -> GrammarBuilder n t'
-- mapGrammar f = fmap f

-- cons :: (Identifiable n, Identifiable t) => t -> [n] -> Rhs n t
-- cons c ts =
--   Rhs { constrs = Constructors
--                 $ Map.singleton c
--                 $ IM.singleton (length ts)
--                 $ Set.singleton ts
--       , epsilons = mempty
--       }

-- -- | @L(addConstructor c [g1...gn]) = [ c(t1...tn) | t1 in L(g1) ... tn in L(gn)]@
-- addConstructor :: (NonTerm n, Identifiable n, Identifiable t) => t -> [GrammarBuilder n t] -> GrammarBuilder n t
-- addConstructor n gs = do
--   s <- fresh
--   gs' <- sequence gs
--   return $ Grammar s $ Map.insert s (cons n (start <$> gs'))
--                      $ foldMap productions gs'

union :: (NonTerminal n, IsGrammar n t) => GrammarBuilder n t -> GrammarBuilder n t -> GrammarBuilder n t
union g1 g2 = do
  Grammar start1 prods1 <- g1
  Grammar start2 prods2 <- g2
  s <- fresh
  return $ Grammar s $ Map.insert s (mempty {eps = [start1, start2]})
                     $ Map.unionWith (error "non terminals are not disjoint") prods1 prods2

-- | Inlines all productions reachable via epsilon rules.
epsilonClosure :: (Identifiable n, IsGrammar n t) => Grammar n t -> Grammar n t
epsilonClosure g@(Grammar _ p) = g { productions = Map.mapWithKey close p } 
  where
    close name rhs =
      Rhs { cons = lookup' name g
          , eps = Set.empty
          }

lookup :: (Foldable f, IsGrammar n t) => f n -> Grammar n t -> t n
lookup n g@(Grammar _ p) = cons $ foldMap (p Map.!) $ epsilonReachable n g

lookup' :: forall n t. IsGrammar n t => n -> Grammar n t -> t n
lookup' n = lookup ([n] :: [n])

-- Computes the set of non-terminals reachable via epsilon rules.
epsilonReachable :: (Foldable f, IsGrammar n t) => f n -> Grammar n t -> HashSet n
epsilonReachable ns (Grammar _ p) = foldl' go Set.empty ns
  where
    go r n
      | Set.member n r = r
      | otherwise      = foldl' go (Set.insert n r) (eps (p Map.! n))

-- | Removes productions that are not reachable from the start symbol.
dropUnreachable :: (Foldable t, IsGrammar n t) => Grammar n t -> Grammar n t
dropUnreachable g@(Grammar s p) =
  g { productions = Map.filterWithKey (\k _ -> Set.member k (reachable' s g)) p }

reachable :: (Foldable f, IsGrammar n t) => f n -> Grammar n t -> HashSet n
reachable ns g = foldl' go Set.empty ns
  where
    go r n
      | Set.member n r = r
      | otherwise      = foldl' go (Set.insert n r) (toList (lookup' n g))

reachable' :: forall t n. IsGrammar n t => n -> Grammar n t -> HashSet n
reachable' n = reachable ([n] :: [n])

dropUnproductive :: IsGrammar n t => Grammar n t -> Grammar n t
dropUnproductive g@(Grammar _ p) =
  g { productions = Map.filterWithKey (\k _ -> Set.member k (productive g)) p }

-- | Returns all productive nonterminals in the given grammar.
productive :: forall n t. IsGrammar n t => Grammar n t -> HashSet n
productive (Grammar _ prods) = go $ Set.fromList [ n | (n, rhs) <- Map.toList prods, T.productive mempty (cons (rhs))]
  where
    go :: HashSet n -> HashSet n
    go p =
      let p' = Set.union p $ Set.fromList [ n | (n, rhs) <- Map.toList prods, rhsProductive rhs p ]
      in if p == p' then p else go p'

    -- A right hand side is productive if one of its epsilon rules is
    -- productive or a all non-terminals of a constructor are productive.
    rhsProductive :: Rhs n t -> HashSet n -> Bool
    rhsProductive rhs prod = any (`Set.member` prod) (eps rhs)
                          || T.productive prod (cons rhs)

type RenameMap n n' = HashMap (HashSet n) n'
determinize :: forall n n' t. (IsGrammar n t, IsGrammar n' t) => Grammar n t -> GrammarBuilder n' t
determinize g@(Grammar s p) = state $ \i ->
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
         let prods = lookup ns g
         ctrs <- T.determinize go prods
         modifyRes $ Map.insert n (Rhs { cons = ctrs, eps = mempty})
         return n

   unique :: State (Gen n',(ProdMap n' t,RenameMap n n')) n'
   unique = state (\(i,x) -> let (f,i') = runState fresh i in (f,(i',x)))

   getRmap :: State (Gen n',(ProdMap n' t',RenameMap n n')) (RenameMap n n')
   getRmap = snd . snd <$> get

   putRmap :: RenameMap n n' -> State (Gen n',(ProdMap n' t',RenameMap n n')) ()
   putRmap r = modify (second (second (const r)))

   modifyRes :: (ProdMap n' t -> ProdMap n' t) -> State (Gen n',(ProdMap n' t,RenameMap n n')) ()
   modifyRes f = modify (second (first f))

-- | Test whether the first grammar is a subset of the second,
-- i.e. whether L(G1) ⊆ L(G2). The return value is either @Nothing@ or
-- a wittness of which non-terminals are a subset of other
-- non-terminals.  For example, if @([A,B],[X,Y]) in subsetOf G1 G2@ then
-- @L(G1(A)) U L(G1(B))  ⊆  L(G2(X)) U L(G2(Y))@.
subsetOf :: forall n1 n2 t. (IsGrammar n1 t, IsGrammar n2 t)
         => Grammar n1 t -> Grammar n2 t -> Maybe [(HashSet n1,HashSet n2)]
g1@(Grammar s1 p1) `subsetOf` g2@(Grammar s2 p2) = fmap (fmap (\(x,y) -> (y,x)) . Map.toList) (execStateT (go [s1] [s2]) mempty)
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
            c1 = lookup m1' g1
            c2 = lookup m2 g2

        T.subsetOf go c1 c2

    subset :: Identifiable a => HashSet a -> HashSet a -> Bool
    subset m1 m2 = all (`Set.member` m2) m1

instance (Identifiable n, Semigroup (t n)) => Semigroup (Rhs n t) where
  Rhs c1 e1 <> Rhs c2 e2 = Rhs (c1 <> c2) (e1 <> e2)
instance (Identifiable n, Monoid (t n)) => Monoid (Rhs n t) where
  mappend = (<>)
  mempty = Rhs { cons = mempty, eps = mempty }
