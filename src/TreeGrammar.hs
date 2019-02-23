{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module TreeGrammar where

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

data Grammar a = Grammar { start :: NonTerm, productions :: ProdMap a }
type ProdMap a = HashMap NonTerm (Rhs a)
data Rhs a = Rhs { constrs :: Constructors a, epsilons :: HashSet NonTerm }
newtype Constructors a = Constructors (HashMap a (IntMap (HashSet [NonTerm])))

type GrammarBuilder a = State Int (Grammar a)

mapGrammar :: (Grammar a -> Grammar b) -> GrammarBuilder a -> GrammarBuilder b
mapGrammar f = fmap f

cons :: Identifiable a => a -> [NonTerm] -> Rhs a
cons c ts =
  Rhs { constrs = Constructors
                $ Map.singleton c
                $ IM.singleton (length ts)
                $ Set.singleton ts
      , epsilons = mempty
      }

-- | @L(addConstructor c [g1...gn]) = [ c(t1...tn) | t1 in L(g1) ... tn in L(gn)]@
addConstructor :: Identifiable a => a -> [GrammarBuilder a] -> GrammarBuilder a
addConstructor n gs = do
  s <- uniqueStart
  gs' <- sequence gs
  return $ Grammar s $ Map.insert s (cons n (start <$> gs'))
                     $ foldMap productions gs'

union :: Identifiable a => GrammarBuilder a -> GrammarBuilder a -> GrammarBuilder a
union g1 g2 = do
  Grammar start1 prods1 <- g1
  Grammar start2 prods2 <- g2
  s <- uniqueStart
  return $ Grammar s $ Map.insert s (mempty {epsilons = [start1, start2]})
                     $ Map.unionWith (error "non terminals are not disjoint") prods1 prods2

-- | Inlines all productions reachable via epsilon rules.
epsilonClosure :: Identifiable a => Grammar a -> Grammar a
epsilonClosure g@(Grammar _ p) = g { productions = Map.mapWithKey close p } 
  where
    close name rhs =
      Rhs { constrs =
              constrs rhs <>
              constrs (foldMap (p Map.!) $ Set.toList (epsilonReachable name p))
          , epsilons = Set.empty
          }

-- Computes the set of non-terminals reachable via epsilon rules.
epsilonReachable :: NonTerm -> ProdMap a -> HashSet NonTerm
epsilonReachable n0 p = go n0 Set.empty
  where
    go :: NonTerm -> HashSet NonTerm -> HashSet NonTerm
    go n r 
      | Set.member n r = r
      | otherwise      = foldl' (flip go) (Set.insert n r) (epsilons (p Map.! n))

lookup :: Identifiable a => NonTerm -> ProdMap a -> Constructors a
lookup n p = constrs $ foldMap (p Map.!) $ Set.toList (epsilonReachable n p)

-- | Removes productions that are not reachable from the start symbol.
dropUnreachable :: Identifiable a => Grammar a -> Grammar a
dropUnreachable g@(Grammar s p) =
  g { productions = Map.filterWithKey (\k _ -> Set.member k (reachable s g)) p }

reachable :: Identifiable a => NonTerm -> Grammar a -> HashSet NonTerm
reachable n0 (Grammar _ p) = go n0 Set.empty
  where
    go :: NonTerm -> HashSet NonTerm -> HashSet NonTerm
    go n r
      | Set.member n r = r
      | otherwise      = foldl' (flip go) (Set.insert n r) (nonTerms (lookup n p))

dropUnproductive :: Grammar a -> Grammar a
dropUnproductive g@(Grammar _ p) =
  g { productions = Map.filterWithKey (\k _ -> Set.member k (productive g)) p }

-- | Returns all productive nonterminals in the given grammar.
productive :: Grammar a -> HashSet NonTerm
productive (Grammar _ prods) = go $ Set.fromList [ n | (n, rhs) <- Map.toList prods, producesConstant rhs]
  where
    producesConstant :: Rhs a -> Bool
    producesConstant rhs = any (any null) (constructors' rhs)
  
    go :: HashSet NonTerm -> HashSet NonTerm
    go p =
      let p' = Set.union p $ Set.fromList [ n | (n, rhs) <- Map.toList prods, rhsProductive rhs p ]
      in if p == p' then p else go p'

    -- A right hand side is productive if one of its epsilon rules is
    -- productive or a all non-terminals of a constructor are productive.
    rhsProductive :: Rhs a -> HashSet NonTerm -> Bool
    rhsProductive rhs prod = any (`Set.member` prod) (epsilons rhs)
                          || any (any (any (all (`Set.member` prod)))) (constructors' rhs)


type RenameMap = HashMap (HashSet NonTerm) NonTerm
determinize :: forall a. Identifiable a => Grammar a -> GrammarBuilder a
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
   go :: Identifiable a => HashSet NonTerm -> State (Int, (ProdMap a,RenameMap)) NonTerm
   go ns = do
     rmap <- getRmap
     case Map.lookup ns rmap of
       Just x -> return x
       Nothing -> do
         n <- unique
         putRmap $ Map.insert ns n rmap
         let Constructors prods = foldMap (\k -> lookup k p) (Set.toList ns)
         ctrs <- traverse (traverse (fmap Set.singleton . traverse go . transpose)) prods
         modifyRes $ Map.insert n (Rhs { constrs = Constructors ctrs, epsilons = mempty})
         return n

   unique :: State (Int,(ProdMap a,RenameMap)) NonTerm
   unique = state (\(i,x) -> let (f,i') = runState uniqueNt i in (f,(i',x)))

   getRmap :: State (Int,(ProdMap a,RenameMap)) RenameMap
   getRmap = snd . snd <$> get

   putRmap :: RenameMap -> State (Int,(ProdMap a,RenameMap)) ()
   putRmap r = modify (second (second (const r)))

   modifyRes :: (ProdMap a -> ProdMap a) -> State (Int,(ProdMap a,RenameMap)) ()
   modifyRes f = modify (second (first f))

   transpose :: Identifiable x => HashSet [x] -> [HashSet x]
   transpose = fmap Set.fromList . L.transpose . Set.toList


class NonTerminals a where
  nonTerms :: a -> HashSet NonTerm

instance NonTerminals [NonTerm] where
  nonTerms = Set.fromList

instance NonTerminals (Grammar a) where
  nonTerms (Grammar _ p) = Set.fromList $ Map.keys p

instance NonTerminals (Rhs a) where
  nonTerms rhs = nonTerms (constrs rhs) <> epsilons rhs

instance NonTerminals n => NonTerminals (HashSet n) where
  nonTerms rhs = foldMap nonTerms rhs

instance NonTerminals n => NonTerminals (HashMap a n) where
  nonTerms m = foldMap nonTerms (Map.elems m)

instance NonTerminals n => NonTerminals (IntMap n) where
  nonTerms m = foldMap nonTerms (IM.elems m)

instance NonTerminals (Constructors a) where
  nonTerms (Constructors m) = nonTerms m

instance Identifiable a => Semigroup (Constructors a) where
  Constructors c1 <> Constructors c2 = Constructors (Map.unionWith (IM.unionWith (<>)) c1 c2)
instance Identifiable a => Monoid (Constructors a) where
  mappend = (<>)
  mempty = Constructors Map.empty

instance Identifiable a => Semigroup (Rhs a) where
  Rhs c1 e1 <> Rhs c2 e2 = Rhs (c1 <> c2) (e1 <> e2)
instance Identifiable a => Monoid (Rhs a) where
  mappend = (<>)
  mempty = Rhs { constrs = mempty, epsilons = mempty }

constructors' :: Rhs a -> HashMap a (IntMap (HashSet [NonTerm]))
constructors' (Rhs {constrs = Constructors c}) = c
