{-# LANGUAGE OverloadedStrings #-}
module TreeAutomataSpec(main, spec) where

import           Control.Monad.State hiding (sequence)

import           Data.List hiding (union)
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Text (Text)

import           TreeAutomata

import           Test.Hspec
import           Test.HUnit

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

  describe "Subterms" $ do
    it "should destruct and rebuild PCF" $ do
      let pcf' = fromSubterms (toSubterms pcf)
      pcf' `shouldSatisfy` isDeterministic
      pcf' `shouldBe` pcf

    it "should destruct and rebuild a nondeterministic grammar" $ do
      let nondet'' = fromSubterms (toSubterms nondet)
      nondet'' `shouldSatisfy` isDeterministic
      nondet'' `shouldBe` nondet

    it "should destruct and rebuild the infinite grammar into the empty grammar" $ do
      fromSubterms (toSubterms infinite) `shouldSatisfy` isEmpty

  describe "Size" $ do
    it "should be 25 on PCF" $
      size pcf `shouldBe` 25

    it "should be 10 on nondet" $
      size nondet `shouldBe` 10

    it "should be defined on an infinite grammar" $
      size infinite `shouldBe` 2

  describe "Height" $ do
    it "should be 11 on PCF" $
      height pcf `shouldBe` 11

    it "should be 5 on nondet" $
      height nondet `shouldBe` 5

    it "should be defined on an infinite grammar" $
      height infinite `shouldBe` 1

  describe "Productivity" $ do
    it "should give all nonterminals for PCF" $ do
      let pcf' = evalState pcf 0
      map (`isProductive` pcf') ["Exp", "Type", "String", "PStart"] `shouldBe` [True, True, True, True]

    it "should give no nonterminals for infinite" $ do
      let infinite' = evalState infinite 0
      map (`isProductive` infinite') ["foo", "EStart"] `shouldBe` [False, False]

    it "should give all nonterminals for a nondeterministic grammar" $ do
      let nondet'' = evalState nondet 0
      map (`isProductive` nondet'') ["S", "A", "G", "F"] `shouldBe` [True, True, True, True]

    it "should give all nonterminals for nondet'" $ do
      let nondet''' = evalState nondet' 0
      map (`isProductive` nondet''') ["S", "A", "G", "H", "F"] `shouldBe` [True, True, True, True, True]

    it "should give all nonterminals for the PCF subset" $ do
      let pcf_sub' = evalState pcf_sub 0
      map (`isProductive` pcf_sub') ["PSStart", "Exp", "Type"] `shouldBe` [True, True, True]

    it "should give all nonterminals for the union of PCF and a nondeterministic grammar" $ do
      let pcf_nondet' = evalState pcf_nondet 0
      map (`isProductive` pcf_nondet') ["Start0", "PStart", "S", "A", "G", "F", "Exp", "Type", "Type"] `shouldBe` [True, True, True, True, True, True, True, True, True]

    it "should correctly compute that PCF produces Zero, Num and String" $
      map (\n -> produces (pcf::GrammarBuilder Text) n) ["Zero", "Num", "String", "Succ", "Pred", "Ifz"] `shouldBe` [True, True, True, False, False, False]

    it "should correctly compute that the infinite grammar does not produce \"foo\"" $
      produces infinite "foo" `shouldBe` False

  describe "Emptiness" $ do
    it "should be true on the infinite infinite grammar" $
      infinite `shouldSatisfy` isEmpty

    it "should be false on the nondeterministic grammar" $
      nondet `shouldNotSatisfy` isEmpty

    it "should be false on the PCF grammar" $
      pcf `shouldNotSatisfy` isEmpty

    it "should be false on the subset of PCF" $
      pcf_sub `shouldNotSatisfy` isEmpty

  describe "Singletoness" $ do
    it "should be false on the infinite infinite grammar" $
      infinite `shouldNotSatisfy` isSingleton

    it "should be false on the nondeterministic grammar" $
      nondet `shouldNotSatisfy` isSingleton

    it "should be false on the PCF grammar" $
      pcf `shouldNotSatisfy` isSingleton

    it "should be true on a singleton grammar" $
      let g :: GrammarBuilder Text
          g = grammar "Foo" (M.fromList [ ("Foo", [ Ctor "Bar" [ "Baz" ] ])
                                        , ("Baz", [ Ctor "Baz" [] ]) ])
      in g `shouldSatisfy` isSingleton

  describe "Union" $ do
    it "should work on the union of two small grammars" $
      let g1 :: GrammarBuilder Text
          g1 = grammar "Foo" $ M.fromList [ ("Foo", [ Ctor "Zero" [] ])]
          g2 :: GrammarBuilder Text
          g2 = grammar "Bar" $ M.fromList [ ("Bar", [ Ctor "Num" [] ])]
          g3 :: GrammarBuilder Text
          g3 = grammar "Start0" $ M.fromList [ ("Start0", [ Eps "Foo", Eps "Bar" ])
                                             , ("Foo", [ Ctor "Zero" [] ])
                                             , ("Bar", [ Ctor "Num" [] ])]
      in union g1 g2 `shouldBeLiteral` g3

    it "should work on the union of the nondeterministic and PCF grammars" $
      union pcf nondet `shouldBeLiteral` pcf_nondet

    it "should produce the same language when taken over identical grammars (PCF)" $ do
      union pcf pcf `shouldBe` pcf

    it "should produce the same language when taken over identical grammars (nondet)" $ do
      union nondet nondet `shouldBe` nondet

  describe "Intersection" $ do
    it "of a subset of the PCF grammar should be that subset" $
      intersection pcf pcf_sub `shouldBeLiteral` (grammar "PStart⨯PSStart" $
                                                  M.fromList [ ("Exp⨯Exp", [ Ctor "Zero" []
                                                                           , Ctor "Succ" ["Exp⨯Exp"]
                                                                           , Ctor "Pred" ["Exp⨯Exp"]])
                                                             , ("PStart⨯PSStart", [ Ctor "Zero" []
                                                                                  , Ctor "Succ" ["Exp⨯Exp"]
                                                                                  , Ctor "Pred" ["Exp⨯Exp"]
                                                                                  , Ctor "Num" []
                                                                                  , Ctor "Fun" [ "Type⨯Type", "Type⨯Type" ]])
                                                             , ("Type⨯Type", [ Ctor "Num" []
                                                                             , Ctor "Fun" [ "Type⨯Type", "Type⨯Type" ]])])

    it "should give an empty grammar if the arguments have no intersection" $ do
      intersection nondet pcf `shouldBeLiteral` (grammar "S⨯PStart" M.empty)

    it "should give an empty grammar when one of the arguments is an empty grammar" $ do
      intersection nondet infinite `shouldBeLiteral` (grammar "S⨯EStart" M.empty)
      intersection infinite nondet `shouldBeLiteral` (grammar "EStart⨯S" M.empty)

  describe "Inclusion" $ do
    it "should work for the worked out (deterministic) example" $
      let g :: GrammarBuilder Text
          g = grammar "S" $ M.fromList [("S", [ Ctor "f" ["A"]
                                              , Ctor "c" []
                                              , Ctor "f" ["B"]])
                                       ,("A", [ Ctor "g" ["S"]
                                              , Ctor "e" []])
                                       ,("B", [ Ctor "b" []])]
          g' :: GrammarBuilder Text
          g' = grammar "S'" $ M.fromList [("S'", [ Ctor "f" ["A'"]
                                                 , Ctor "c" []
                                                 , Ctor "f" ["B'"]])
                                         ,("A'", [ Ctor "g" ["S'"]
                                                 , Ctor "e" []])
                                         ,("B'", [ Ctor "b" []])]
      in g `shouldSatisfy` subsetOf g'

    it "should be true for the PCF grammar and a subset of the PCF grammar" $ do
      pcf_sub `shouldSatisfy` (`subsetOf` pcf)
      pcf `shouldNotSatisfy` (`subsetOf` pcf_sub)

    it "reflexivity should hold on PCF" $
      pcf `shouldSatisfy` subsetOf pcf

    it "reflexivity should hold on the nondeterministic grammar" $
      determinize nondet `shouldSatisfy` subsetOf (determinize nondet)

    it "should not hold for languages that do not intersect" $ do
      determinize nondet `shouldNotSatisfy` subsetOf pcf
      pcf `shouldNotSatisfy` subsetOf (determinize nondet)

  describe "Equality" $ do
    it "should be true when comparing the same grammar" $ do
      pcf `shouldBe` pcf

    it "should be true when comparing the same grammar (nondet)" $ do
      nondet `shouldBe` nondet

    it "should be false when comparing different grammars" $ do
      pcf `shouldNotBe` nondet

    it "should be true when comparing different grammars producing the same language" $ do
      nondet `shouldBe` nondet'

  describe "Integration tests" $ do
    it "union idempotence should hold for the nondeterministic grammar" $
      union nondet nondet `shouldBe` nondet

    it "union idempotence should hold for PCF" $
      union pcf pcf `shouldBe` pcf

    it "intersection of a subset should be that subset" $
      intersection pcf pcf_sub `shouldBe` pcf_sub

    it "union absorption should hold" $
      union pcf (intersection pcf nondet) `shouldBe` pcf

    it "intersection idempotence should hold for PCF" $
      intersection pcf pcf `shouldBe` pcf

    it "intersection idempotence should hold for the nondeterministic grammar" $
      intersection nondet nondet `shouldBe` nondet

    it "intersection absorption should hold" $
      intersection pcf (union pcf nondet) `shouldBe` pcf

  describe "Alphabet" $ do
    it "should correctly list the alphabet of PCF" $
      let a = M.fromList [("App", [2]), ("Abs", [3]), ("Zero", [0]), ("Succ", [1]), ("Pred", [1]), ("Ifz", [3]), ("Num", [0]), ("Fun", [2]), ("String", [0])]
      in alphabet pcf `shouldBe` a

  describe "Normalization" $ do
    it "should work on an empty grammar" $ do
      let empty :: GrammarBuilder Text
          empty = grammar "S" $ M.fromList [ ("S", []) ]
      dropUnreachable empty `shouldBeLiteral` empty
      dropEmpty empty `shouldBeLiteral` grammar "S" M.empty
      normalize empty `shouldBeLiteral` grammar "S" M.empty

  describe "Determinization" $ do
    it "should work on an empty grammar" $ do
      let empty :: GrammarBuilder Text
          empty = grammar "S" $ M.fromList [ ("S", []) ]
      empty `shouldSatisfy` isDeterministic
      determinize empty `shouldBe` empty

    it "should correctly determinize PCF" $ do
      let det = determinize pcf
      det `shouldSatisfy` isDeterministic
      det `shouldBe` pcf
      determinize det `shouldBe` pcf

    it "should correctly determinize the nondeterministic grammar" $ do
      let det = determinize nondet
      nondet `shouldNotSatisfy` isDeterministic
      nondet' `shouldNotSatisfy` isDeterministic
      det `shouldSatisfy` isDeterministic
      det `shouldBe` nondet

    it "should correctly determinize another nondeterministic grammar" $ do
      let ng :: GrammarBuilder Text
          ng = grammar "S" $ M.fromList [ ("S", [ Ctor "foo" [], Ctor "foo" [] ]) ]
          det = determinize ng
      ng `shouldNotSatisfy` isDeterministic
      det `shouldSatisfy` isDeterministic
      det `shouldBe` ng

    it "should correctly determinize another nondeterministic grammar" $ do
      let ng :: GrammarBuilder Text
          ng = grammar "S" $ M.fromList [ ("S", [ Ctor "foo" [ "A", "B" ] ])
                                        , ("A", [ Ctor "bar" [ "C" ]
                                                , Ctor "bar" [ "D" ]])
                                        , ("B", [ Ctor "baz" [ "E" ]
                                                , Ctor "baz" [ "F" ]])
                                        , ("C", [ Ctor "c" [] ])
                                        , ("D", [ Ctor "d" [] ])
                                        , ("E", [ Ctor "e" [] ])
                                        , ("F", [ Ctor "f" [] ])]
          det = determinize ng
      ng `shouldNotSatisfy` isDeterministic
      det `shouldSatisfy` isDeterministic
      det `shouldBe` ng

    it "should correctly determinize the infinite grammar" $ do
      let det = determinize infinite
      det `shouldSatisfy` isDeterministic
      det `shouldBe` infinite

  describe "Widening" $ do
    it "wideMap should compute the depths and principal label sets of nonterminals in PCF" $ do
      let pcf' = evalState pcf 0
          pcf_wideMap = wideMap pcf'
          pcf_prods = productions pcf'
      M.lookup "PStart" pcf_wideMap `shouldBe` Just (0,S.empty,pcf_prods M.! "PStart")
      M.lookup "Exp" pcf_wideMap `shouldBe` Just (1,S.fromList ["App","Abs","Zero","Succ","Pred","Ifz"],pcf_prods M.! "Exp")
      M.lookup "String" pcf_wideMap `shouldBe` Just (2,S.singleton "String",pcf_prods M.! "String")
      M.lookup "Type" pcf_wideMap `shouldBe` Just (1,S.fromList ["Num","Fun"],pcf_prods M.! "Type")

    it "wideMap should compute the depths and principal label sets of nonterminals in the nondeterministic grammar" $ do
      let nondet'' = evalState nondet' 0
          nondet_wideMap = wideMap nondet''
          nondet_prods = productions nondet''
      M.lookup "S" nondet_wideMap `shouldBe` Just (0,S.empty,nondet_prods M.! "S")
      M.lookup "F" nondet_wideMap `shouldBe` Just (1,S.singleton "f",nondet_prods M.! "F")
      M.lookup "G" nondet_wideMap `shouldBe` Just (2,S.singleton "g",nondet_prods M.! "G")
      M.lookup "H" nondet_wideMap `shouldBe` Just (2,S.empty,nondet_prods M.! "H")
      M.lookup "A" nondet_wideMap `shouldBe` Just (3,S.singleton "a",nondet_prods M.! "A")

    it "should build a correspondence set on the example from the paper" $ do
      let cons0' = evalState (epsilonClosure cons0) 0
          cons1' = evalState (epsilonClosure cons1) 0
          cons_w0 = wideMap cons0'
          cons_w1 = wideMap cons1'
      correspondenceSet (start cons0') cons_w0 (start cons1') cons_w1 `shouldBe` M.fromList [(("T0","T3"),S.empty)
                                                                                            ,(("T1","T4"),S.singleton ("cons","T3",0))
                                                                                            ,(("T2","T5"),S.singleton ("cons","T3",1))]

    it "should build a correspondence set on the PCF grammar " $ do
      let pcf_sub' = evalState (epsilonClosure pcf_sub) 0
          pcf' = evalState (epsilonClosure pcf) 0
          pcf_sub_w = wideMap pcf_sub'
          pcf_w = wideMap pcf'
      correspondenceSet (start pcf_sub') pcf_sub_w (start pcf') pcf_w `shouldBe` M.fromList [(("PSStart","PStart"),S.empty)]

    it "should build a correspondence set on the arithmetic example from the paper" $ do
      let arith0' = evalState (epsilonClosure arith0) 0
          arith1' = evalState (epsilonClosure arith1) 0
          arith_w0 = wideMap arith0'
          arith_w1 = wideMap arith1'
      correspondenceSet (start arith0') arith_w0 (start arith1') arith_w1 `shouldBe` M.fromList [(("T0","Tn"),S.empty)
                                                                                                ,(("Tx","T3"),S.fromList [("Add","Tn",0)
                                                                                                                         ,("par","T7",0)])
                                                                                                ,(("T1","T6"),S.fromList [("Add","Tn",1)
                                                                                                                         ,("Mul","T6",0)])
                                                                                                ,(("T2","T7"),S.singleton ("Mul","T6",1))]

    it "should find a set of widening topological clashes on the example from the paper" $ do
      let cons0' = evalState (epsilonClosure cons0) 0
          cons1' = evalState (epsilonClosure cons1) 0
          cons_w0 = wideMap cons0'
          cons_w1 = wideMap cons1'
          corr = correspondenceSet (start cons0') cons_w0 (start cons1') cons_w1
      wideningClashes corr cons_w0 cons_w1 `shouldBe` M.fromList [(("T2","T5"),S.singleton ("cons","T3",1))]

    it "should find a set of widening topological clashes on the PCF grammar" $ do
      let pcf_sub' = evalState (epsilonClosure pcf_sub) 0
          pcf' = evalState (epsilonClosure pcf) 0
          pcf_sub_w = wideMap pcf_sub'
          pcf_w = wideMap pcf'
          corr = correspondenceSet (start pcf_sub') pcf_sub_w (start pcf') pcf_w
      wideningClashes corr pcf_sub_w pcf_w `shouldBe` M.fromList [(("PSStart","PStart"),S.empty)]

    it "should find a set of widening topological clashes on the arithmetic example from the paper" $ do
      let arith0' = evalState (epsilonClosure arith0) 0
          arith1' = evalState (epsilonClosure arith1) 0
          arith_w0 = wideMap arith0'
          arith_w1 = wideMap arith1'
          corr = correspondenceSet (start arith0') arith_w0 (start arith1') arith_w1
      wideningClashes corr arith_w0 arith_w1 `shouldBe` M.fromList [(("Tx","T3"),S.fromList [("Add","Tn",0)
                                                                                            ,("par","T7",0)])]

    it "should find ancestors for the example from the paper" $ do
      let cons1' = evalState cons1 0
          w = wideMap cons1'
      findAncestors "T5" w cons1' `shouldBe` ["T3"]

    it "should find ancestors for the arithmetic example from the paper" $ do
      let arith1' = evalState arith1 0
          w = wideMap arith1'
      findAncestors "T3" w arith1' `shouldBe` ["T6","T7","Tn"]

    it "should find ancestors for PCF" $ do
      let pcf' = evalState pcf 0
          w = wideMap pcf'
      findAncestors "PStart" w pcf' `shouldBe` []
      findAncestors "Exp" w pcf' `shouldBe` ["PStart"]
      findAncestors "String" w pcf' `shouldBe` ["Exp","PStart"]
      findAncestors "Type" w pcf' `shouldBe` ["Exp","PStart"]

    it "should find ancestors for the nondeterministic grammar" $ do
      let nondet'' = evalState nondet' 0
          w = wideMap nondet''
      findAncestors "G" w nondet'' `shouldBe` ["F", "H", "S"]
      findAncestors "A" w nondet'' `shouldBe` ["F", "G", "H", "S"]

    it "should find the best arc ancestor for the example from the paper" $ do
      let cons0' = evalState (epsilonClosure cons0) 0
          cons1' = evalState (epsilonClosure cons1) 0
          w0 = wideMap cons0'
          w1 = wideMap cons1'
          ancs = findAncestors "T5" w1 cons1'
      arcAncestor "T2" "T5" ancs w0 w1 cons1' `shouldBe` Just "T3"

    it "should find the best arc ancestor for the arithmetic example from the paper" $ do
      let arith0' = evalState (epsilonClosure arith0) 0
          arith1' = evalState (epsilonClosure arith1) 0
          w0 = wideMap arith0'
          w1 = wideMap arith1'
          ancs = findAncestors "T3" w1 arith1'
      arcAncestor "Tx" "T3" ancs w0 w1 arith1' `shouldBe` Just "Tn"

    it "should find the best arc ancestor for PCF" $ do
      let pcf' = evalState (epsilonClosure pcf) 0
          w1 = wideMap pcf'
      arcAncestor "PSStart" "PStart" (findAncestors "PStart" w1 pcf') w1 w1 pcf' `shouldBe` Nothing
      arcAncestor "Exp" "Exp" (findAncestors "Exp" w1 pcf') w1 w1 pcf' `shouldBe` Just "PStart"
      arcAncestor "String" "String" (findAncestors "String" w1 pcf') w1 w1 pcf' `shouldBe` Nothing
      arcAncestor "Type" "Type" (findAncestors "Type" w1 pcf') w1 w1 pcf' `shouldBe` Just "PStart"

    it "should find a set of arc replacements for the widening topological clashes for the example from the paper" $ do
      let cons0' = evalState (epsilonClosure cons0) 0
          cons1' = evalState (epsilonClosure cons1) 0
          w0 = wideMap cons0'
          w1 = wideMap cons1'
          corr = correspondenceSet (start cons0') w0 (start cons1') w1
          wideClashes01 = wideningClashes corr w0 w1
      arcReplacements cons1' wideClashes01 w0 w1 `shouldBe` M.fromList [(("T5","T3"),S.singleton ("cons","T3",1))]

    it "should find a set of arc replacements for the widening topological clashes for the PCF grammar" $ do
      let pcf_sub' = evalState (epsilonClosure pcf_sub) 0
          pcf' = evalState (epsilonClosure pcf) 0
          w0 = wideMap pcf_sub'
          w1 = wideMap pcf'
          corr = correspondenceSet (start pcf_sub') w0 (start pcf') w1
          wideClashes = wideningClashes corr w0 w1
      arcReplacements pcf' wideClashes w0 w1 `shouldBe` M.fromList []

    it "should find a set of arc replacements for the widening topological clashes for the arithmetic example from the paper " $ do
      let arith0' = evalState (epsilonClosure arith0) 0
          arith1' = evalState (epsilonClosure arith1) 0
          w0 = wideMap arith0'
          w1 = wideMap arith1'
          corr = correspondenceSet (start arith0') w0 (start arith1') w1
          wideClashes = wideningClashes corr w0 w1
      arcReplacements arith1' wideClashes w0 w1 `shouldBe` M.fromList [(("T3","Tn"),S.fromList [("Add","Tn",0)
                                                                                               ,("par","T7",0)])]

    it "should replace nonterminals with ancestors" $ do
      let consr :: GrammarBuilder Text
          consr = grammar "T3" $ M.fromList [ ("T3", [ Ctor "nil" [], Ctor "cons" ["T4","T3"] ])
                                            , ("T4", [ Ctor "any" [] ])
                                            , ("T6", [ Ctor "any" [] ])
                                            , ("T7", [ Ctor "nil" [] ])]
          cons1' = evalState (epsilonClosure cons1) 0
      return (replaceNonterm "T5" "T3" cons1') `shouldBeLiteral` consr

    it "should replace an edge" $ do
      let consr :: GrammarBuilder Text
          consr = grammar "T3" $ M.fromList [ ("T3", [ Ctor "nil" [], Ctor "cons" ["T4","T3"] ])
                                            , ("T4", [ Ctor "any" [] ])
                                            , ("T5", [ Ctor "nil" [], Ctor "cons" ["T6","T7"] ])
                                            , ("T6", [ Ctor "any" [] ])
                                            , ("T7", [ Ctor "nil" [] ])]
          cons1' = evalState (epsilonClosure cons1) 0
      return (replaceEdge "cons" "T3" 1 "T3" cons1') `shouldBeLiteral` consr

    it "should work on the examples from the paper" $ do
      widen' cons0 cons1 `shouldBeLiteral` cons01
      widen' cons1 cons2 `shouldBeLiteral` cons12
      widen' arith0 arith1 `shouldBe` arith01
      widen' arith1 (widen' arith0 arith1) `shouldBeLiteral` arith01
      widen' arith2 arith3 `shouldBeLiteral` arith3

    it "should be an upper bound" $ do
      let w_cons = widen' cons0 cons1
          w_pcf = widen' pcf_sub pcf
          w_arith = widen' arith0 arith1
      pcf `shouldSatisfy` (`subsetOf` w_pcf)
      pcf_sub `shouldSatisfy` (`subsetOf` w_pcf)
      cons0 `shouldSatisfy` subsetOf w_cons
      cons1 `shouldSatisfy` subsetOf w_cons
      arith0 `shouldSatisfy` subsetOf w_arith
      arith1 `shouldSatisfy` subsetOf w_arith

  where
    nondet = grammar "S" $ M.fromList [ ("S", [ Eps "F" ])
                                      , ("A", [ Ctor "a" [] ])
                                      , ("G", [ Ctor "g" [ "G" ]
                                              , Ctor "g" [ "A" ]])
                                      , ("F", [ Ctor "f" [ "G", "G" ]])]
    nondet' = grammar "S" $ M.fromList [ ("S", [ Eps "F" ])
                                       , ("A", [ Ctor "a" [] ])
                                       , ("G", [ Ctor "g" [ "G" ]
                                               , Ctor "g" [ "A" ]])
                                       , ("H", [ Eps "G" ])
                                       , ("F", [ Ctor "f" [ "G", "H" ]])]
    infinite = grammar "EStart" $ M.fromList [ ("EStart", [ Ctor "Bar" ["EStart"]])]
    pcf = grammar "PStart" $ M.fromList [ ("PStart", [ Eps "Exp"
                                                     , Eps "Type" ])
                                        , ("Exp", [ Ctor "App" ["Exp", "Exp"]
                                                  , Ctor "Abs" ["String", "Type", "Exp"]
                                                  , Ctor "Zero" []
                                                  , Ctor "Succ" ["Exp"]
                                                  , Ctor "Pred" ["Exp"]
                                                  , Ctor "Ifz" ["Exp", "Exp", "Exp"]])
                                        , ("Type", [ Ctor "Num" []
                                                   , Ctor "Fun" ["Type", "Type"]])
                                        , ("String", [ Ctor "String" [] ])]
    pcf_sub = grammar "PSStart" $ M.fromList [ ("PSStart", [ Eps "Exp"
                                                           , Eps "Type" ])
                                             , ("Exp", [ Ctor "Succ" [ "Exp" ]
                                                       , Ctor "Pred" [ "Exp" ]
                                                       , Ctor "Zero" []])
                                             , ("Type", [ Ctor "Num" []
                                                        , Ctor "Fun" ["Type", "Type"]])]
    pcf_nondet = grammar "Start0" $ M.fromList [ ("Start0", [ Eps "PStart"
                                                            , Eps "S" ])
                                               , ("PStart", [ Eps "Exp"
                                                            , Eps "Type" ])
                                               , ("S", [ Eps "F" ])
                                               , ("A", [ Ctor "a" [] ])
                                               , ("G", [ Ctor "g" [ "G" ]
                                                       , Ctor "g" [ "A" ]])
                                               , ("F", [ Ctor "f" [ "G", "G" ]])
                                               , ("Exp", [ Ctor "App" ["Exp","Exp"]
                                                         , Ctor "Abs" ["String", "Type", "Exp"]
                                                         , Ctor "Zero" []
                                                         , Ctor "Succ" ["Exp"]
                                                         , Ctor "Pred" ["Exp"]
                                                         , Ctor "Ifz" ["Exp", "Exp", "Exp"]])
                                               , ("Type", [ Ctor "Num" []
                                                          , Ctor "Fun" ["Type","Type"]])
                                               , ("String", [ Ctor "String" [] ])]

    cons0 :: GrammarBuilder Text
    cons0 = grammar "T0" $ M.fromList [ ("T0", [ Ctor "nil" [], Ctor "cons" ["T1","T2"] ])
                                      , ("T1", [ Ctor "any" [] ])
                                      , ("T2", [ Ctor "nil" [] ])]
    cons1 :: GrammarBuilder Text
    cons1 = grammar "T3" $ M.fromList [ ("T3", [ Ctor "nil" [], Ctor "cons" ["T4","T5"] ])
                                      , ("T4", [ Ctor "any" [] ])
                                      , ("T5", [ Ctor "nil" [], Ctor "cons" ["T6","T7"] ])
                                      , ("T6", [ Ctor "any" [] ])
                                      , ("T7", [ Ctor "nil" [] ])]
    cons2 :: GrammarBuilder Text
    cons2 = grammar "T8" $ M.fromList [ ("T8", [ Ctor "nil" [], Ctor "cons" ["T9","T10"] ])
                                      , ("T9", [ Ctor "any" [] ])
                                      , ("T10", [ Ctor "nil" [], Ctor "cons" ["T11","T12"] ])
                                      , ("T11", [ Ctor "any" [] ])
                                      , ("T12", [ Ctor "nil" [], Ctor "cons" ["T13","T14"] ])
                                      , ("T13", [ Ctor "any" [] ])
                                      , ("T14", [ Ctor "nil" [] ])]
    cons01 :: GrammarBuilder Text
    cons01 = grammar "T3" $ M.fromList [ ("T3", [ Ctor "nil" [], Ctor "cons" ["T4", "T3"] ])
                                       , ("T4", [ Ctor "any" [] ])]
    cons12 :: GrammarBuilder Text
    cons12 = grammar "T8" $ M.fromList [ ("T8", [ Ctor "nil" [], Ctor "cons" ["T9", "T10"] ])
                                       , ("T9", [ Ctor "any" [] ])
                                       , ("T10", [ Ctor "nil" [], Ctor "cons" ["T11", "T10"] ])
                                       , ("T11", [ Ctor "any" [] ])]

    arith0 :: GrammarBuilder Text
    arith0 = grammar "T0" $ M.fromList [ ("T0", [ Ctor "zero" [], Ctor "Add" ["Tx", "T1"] ])
                                       , ("Tx", [ Ctor "zero" [] ])
                                       , ("T1", [ Ctor "one" [], Ctor "Mul" ["T1","T2"] ])
                                       , ("T2", [ Ctor "cst" [], Ctor "par" ["Tx"], Ctor "var" [] ])]
    arith1 :: GrammarBuilder Text
    arith1 = grammar "Tn" $ M.fromList [ ("Tn", [ Ctor "zero" [], Ctor "Add" ["T3","T6"] ])
                                       , ("T3", [ Ctor "zero" [], Ctor "Add" ["Tx","T4"] ])
                                       , ("Tx", [ Ctor "Zero" [] ])
                                       , ("T4", [ Ctor "one" [], Ctor "Mul" ["T4","T5"] ])
                                       , ("T5", [ Ctor "cst" [], Ctor "par" ["Tx"], Ctor "var" [] ])
                                       , ("T6", [ Ctor "one" [], Ctor "Mul" ["T6","T7"] ])
                                       , ("T7", [ Ctor "cst" [], Ctor "par" ["T3"], Ctor "var" [] ])]
    arith2 :: GrammarBuilder Text
    arith2 = grammar "T0" $ M.fromList [ ("T0", [ Ctor "cst" [], Ctor "var" [] ]) ]
    arith3 :: GrammarBuilder Text
    arith3 = grammar "Tn" $ M.fromList [ ("Tn", [ Ctor "cst" [], Ctor "par" ["Tx"], Ctor "var" [] ])
                                       , ("Tx", [ Ctor "zero" [] ]) ]
    arith01 :: GrammarBuilder Text
    arith01 = grammar "Tn" $ M.fromList [ ("Tn", [ Ctor "zero" [], Ctor "Add" ["Tn","T6"] ])
                                        , ("T6", [ Ctor "one" [], Ctor "Mul" ["T6","T7"] ])
                                        , ("T7", [ Ctor "var" [], Ctor "par" ["Tn"], Ctor "cst" [] ])]

    -- Because equality is implemented using inclusion, we cannot test
    -- these functions by using `shouldBe`, which uses the Eq type
    -- class, which uses our equality. This dependency chain results
    -- in unreliable outcomes in the unit tests. We break this by
    -- directly comparing the in-memory representation of the
    -- grammars, which we can do because we know exactly what these
    -- should look like. In fact, this is an even stricter test than
    -- simply comparing grammars using `==`, because we now also
    -- detect spurious non-terminal symbols and production rules.
    shouldBeLiteral :: (Ord a, Show a) => GrammarBuilder a -> GrammarBuilder a -> Expectation
    actual `shouldBeLiteral` expected =
      unless (start actual' == start expected' && productions' actual' == productions' expected')
        (assertFailure $ "Grammars are not literally equal.\nExpected:\n\n" ++ show expected ++ "\nbut got:\n\n" ++ show actual)
      where
        expected' = evalState expected 0
        actual' = evalState actual 0
        productions' g = M.map sort (productions g)
