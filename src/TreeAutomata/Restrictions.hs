module TreeAutomata.Restrictions where
-- TODO: rename to Grammar or CFG

import Control.Monad.Error
import Control.Monad.State
import Data.List
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map

import TreeAutomata
import TreeAutomata.Exp
import TreeAutomata.Optimizations

-- Add productions for all terminals named in the grammar (assumes terminal names start with '"')
addTerminals :: Grammar -> Grammar
addTerminals (Grammar start prods) = Grammar start (Map.fromList $ Map.toList prods ++ terminals) where
  terminals = nub $ sort $
    [(t, [Ctor t []]) | (_,  rhs) <- Map.toList prods, t@('"':_) <- concatMap rhsNames rhs]

anyButOneGrammar ctorInfo name alt ctors =
  Grammar name (Map.fromList [(name, [Ctor c (replicate n alt) | (c, n) <- Map.assocs ctorInfo, c `notElem` ctors])])

anyGrammar ctorInfo name = anyButGrammar ctorInfo name []

anyButGrammar ctorInfo name ctors = anyButOneGrammar ctorInfo name name ctors

leftAssoc' :: CtorInfo -> [Ctor] -> Grammar
leftAssoc' ctorInfo cs = expToTA ctorInfo (leftAssocExp ctorInfo cs)

leftAssocExp ctorInfo cs = exp where
  exp = Neg (Seq "s1" (Any "s1") (orExp "leftAssoc" violations))
  violations = [ Cons c1 ((replicate (i1-1) Wild) ++ [Cons c2 (replicate i2 Wild)]) |
                 c1 <- cs,
                 c2 <- cs,
                 let i1 = Map.findWithDefault (error "leftAssoc.c1") c1 ctorInfo,
                 let i2 = Map.findWithDefault (error "leftAssoc.c2") c2 ctorInfo]

rightAssoc' :: CtorInfo -> [Ctor] -> Grammar
rightAssoc' ctorInfo cs = expToTA ctorInfo exp where
  exp = Neg (Seq "s1" (Any "s1") (orExp "rightAssoc" violations))
  violations = [ Cons c1 (Cons c2 (replicate i2 Wild) : replicate (i1-1) Wild) |
                 c1 <- cs,
                 c2 <- cs,
                 let i1 = Map.findWithDefault (error "rightAssoc.c1") c1 ctorInfo,
                 let i2 = Map.findWithDefault (error "rightAssoc.c2") c2 ctorInfo]

leftAssoc :: CtorInfo -> [Ctor] -> Grammar
leftAssoc ctorInfo cs = Grammar ab (pAB +++ p +++ pABO) where
  Grammar ab pAB = anyButGrammar ctorInfo "Any" cs
  p = Map.fromList [("Any", [Ctor c ((replicate (n-1) "Any") ++ [abo]) | (c, n) <- Map.assocs ctorInfo, c `elem` cs])]
  Grammar abo pABO = anyButOneGrammar ctorInfo "NoCtor" ab cs

rightAssoc :: CtorInfo -> [Ctor] -> Grammar
rightAssoc ctorInfo cs = Grammar ab (pAB +++ p +++ pABO) where
  Grammar ab pAB = anyButGrammar ctorInfo "Any" cs
  p = Map.fromList [("Any", [Ctor c ([abo] ++ (replicate (n-1) "Any")) | (c, n) <- Map.assocs ctorInfo, c `elem` cs])]
  Grammar abo pABO = anyButOneGrammar ctorInfo "NoCtor" ab cs

assocs :: CtorInfo -> [(Bool, [Ctor])] -> [Grammar]
assocs ctorInfo [] = []
assocs ctorInfo ((isLeft, ctors) : rest) = f ctorInfo ctors : assocs ctorInfo rest where
  f = if isLeft then leftAssoc else rightAssoc

assocs' :: CtorInfo -> [(Bool, [Ctor])] -> [Grammar]
assocs' ctorInfo [] = []
assocs' ctorInfo ((isLeft, ctors) : rest) = f ctorInfo ctors : assocs ctorInfo rest where
  f = if isLeft then leftAssoc' else rightAssoc'

strictPrecidence ctorInfo css = {-normalize $-} epsilonClosure $ Grammar ab ({-pAB `unionProds`-} pAB' `unionProds` p) where
  name i = "Prec" ++ show i
  --Grammar ab pAB = anyButGrammar ctorInfo "Any" (concat css)
  ab = name 1
  Grammar _ pAB' = anyButOneGrammar ctorInfo (name ((length css) + 1)) ab (concat css)
  p = (Map.fromList $ [(ab, [Eps (name 1)])]) `unionProds`
      (Map.fromList $ concat $ zipWith f [1..] css)
  f i cs =
    [(name i, [Eps (name (i+1))] ++
              [Ctor c (take n (repeat (name (i+1)))) |
               (c, n) <- Map.assocs ctorInfo, c `elem` cs])]

precidence = precidenceGen f where
  f j c i = Just j

-- h returning Nothing means break out of the precidence hierarchy
-- h returning Just means go to that precidence level
precidenceGen :: (Int -> Ctor -> Arity -> Maybe Int) -> CtorInfo -> [[Name]] -> Grammar
precidenceGen h ctorInfo css = {-normalize $-} epsilonClosure $ Grammar ab ({-pAB `unionProds`-} pAB' `unionProds` p) where
  name i = "Prec" ++ show i
  --Grammar ab pAB = anyButGrammar ctorInfo "Any" (concat css)
  ab = name 1
  Grammar _ pAB' = anyButOneGrammar ctorInfo (name ((length css) + 1)) ab (concat css)
  p = (Map.fromList $ [(ab, [Eps (name 1)])]) `unionProds`
      (Map.fromList $ concat $ zipWith f [1..] css)
  f i cs =
    [(name i, [Eps (name (i+1))] ++
              [Ctor c [case h i c j of Nothing -> ab; Just k -> name k | j <- [0 .. n-1]] |
               (c, n) <- Map.assocs ctorInfo, c `elem` cs])]


{-
abstractDecl_C99 g = epsilonClosure $ Grammar s (p' ++ add) where
  Grammar s p' = g `intersectGrammar` Grammar def (pDef ++ p)
  Grammar def pDef = anyButGrammar g "Def" ["AbstractParameter", "TypeName"]
  add = [("(declarator,Abs)", Eps "(pointer,Def)"),
         ("(direct-declarator,Abs)", Ctor "eps" [])]
  --  (then remove "eps" from "Pointer")
  abs = "Abs"

  p = [(def, Ctor "AbstractParameter" [def, abs]),
       (def, Ctor "TypeName" [def, abs]),

       (abs, Ctor "Pointer" [def, abs]),
       (abs, Ctor "Parens" [def{-(-}, abs, def{-)-}]),
       (abs, Ctor "ArrayDeclarator" [abs, def{-[-}, def, def, def{-]-}]),
       (abs, Ctor "ArrayStaticDeclarator1" [abs, def{-[-}, def{-static-}, def, def, def{-]-}]),
       (abs, Ctor "ArrayStaticDeclarator2" [abs, def{-[-}, def, def{-static-}, def, def{-]-}]),
       (abs, Ctor "FunctionDeclarator1" [abs, def{-(-}, def, def{-)-}])]
-}
