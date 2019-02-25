{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module TreeGrammarSpec(main, spec) where

import           Control.Monad
import           Control.Exception (try,ErrorCall)

import           TreeGrammar
import           Terminal(Constr)
import           NonTerminal(Named)

import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck

import           GHC.Exts
import           Text.Printf

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

  -- describe "Subterms" $ do
  --   it "should destruct and rebuild PCF" $ do
  --     let pcf' = fromSubterms (toSubterms pcf)
  --     pcf' `shouldSatisfy` isDeterministic
  --     pcf' `shouldBe` pcf

  --   it "should destruct and rebuild a nondeterministic grammar" $ do
  --     let nondet'' = fromSubterms (toSubterms nondet)
  --     nondet'' `shouldSatisfy` isDeterministic
  --     nondet'' `shouldBe` nondet

  --   it "should destruct and rebuild the infinite grammar into the empty grammar" $ do
  --     fromSubterms (toSubterms infinite) `shouldSatisfy` isEmpty

  -- describe "Size" $ do
  --   it "should be 25 on PCF" $
  --     size pcf `shouldBe` 25

  --   it "should be 10 on nondet" $
  --     size nondet `shouldBe` 10

  --   it "should be defined on an infinite grammar" $
  --     size infinite `shouldBe` 2

  -- describe "Height" $ do
  --   it "should be 11 on PCF" $
  --     height pcf `shouldBe` 11

  --   it "should be 5 on nondet" $
  --     height nondet `shouldBe` 5

  --   it "should be defined on an infinite grammar" $
  --     height infinite `shouldBe` 1

  -- describe "Productivity" $ do
  --   it "should give all nonterminals for PCF" $ do
  --     (`productive` pcf) ["Exp", "Type", "String", "PStart"] `shouldBe` [True, True, True, True]

  --   it "should give no nonterminals for infinite" $ do
  --     let infinite' = evalState infinite 0
  --     map (`isProductive` infinite') ["foo", "EStart"] `shouldBe` [False, False]

  --   it "should give all nonterminals for a nondeterministic grammar" $ do
  --     let nondet'' = evalState nondet 0
  --     map (`isProductive` nondet'') ["S", "A", "G", "F"] `shouldBe` [True, True, True, True]

  --   it "should give all nonterminals for nondet'" $ do
  --     let nondet''' = evalState nondet' 0
  --     map (`isProductive` nondet''') ["S", "A", "G", "H", "F"] `shouldBe` [True, True, True, True, True]

  --   it "should give all nonterminals for the PCF subset" $ do
  --     let pcf_sub' = evalState pcf_sub 0
  --     map (`isProductive` pcf_sub') ["PSStart", "Exp", "Type"] `shouldBe` [True, True, True]

  --   it "should give all nonterminals for the union of PCF and a nondeterministic grammar" $ do
  --     let pcf_nondet' = evalState pcf_nondet 0
  --     map (`isProductive` pcf_nondet') ["Start0", "PStart", "S", "A", "G", "F", "Exp", "Type", "Type"] `shouldBe` [True, True, True, True, True, True, True, True, True]

  --   it "should correctly compute that PCF produces Zero, Num and String" $
  --     map (\n -> produces (pcf::GrammarBuilder Text) n) ["Zero", "Num", "String", "Succ", "Pred", "Ifz"] `shouldBe` [True, True, True, False, False, False]

  --   it "should correctly compute that the infinite grammar does not produce \"foo\"" $
  --     produces infinite "foo" `shouldBe` False

  -- describe "Emptiness" $ do
  --   it "should be true on the infinite infinite grammar" $
  --     infinite `shouldSatisfy` isEmpty

  --   it "should be false on the nondeterministic grammar" $
  --     nondet `shouldNotSatisfy` isEmpty

  --   it "should be false on the PCF grammar" $
  --     pcf `shouldNotSatisfy` isEmpty

  --   it "should be false on the subset of PCF" $
  --     pcf_sub `shouldNotSatisfy` isEmpty

  -- describe "Singletoness" $ do
  --   it "should be false on the infinite infinite grammar" $
  --     infinite `shouldNotSatisfy` isSingleton

  --   it "should be false on the nondeterministic grammar" $
  --     nondet `shouldNotSatisfy` isSingleton

  --   it "should be false on the PCF grammar" $
  --     pcf `shouldNotSatisfy` isSingleton

  --   it "should be true on a singleton grammar" $
  --     let g :: GrammarBuilder Text
  --         g = grammar "Foo" (M.fromList [ ("Foo", [ Ctor "Bar" [ "Baz" ] ])
  --                                       , ("Baz", [ Ctor "Baz" [] ]) ])
  --     in g `shouldSatisfy` isSingleton

  describe "Union" $ do

    it "should work for non deterministic grammars" $
      union pcf nondet `shouldBe` pcf_nondet

    prop "should be idempotent: G ∪ G = G" $ \(g :: GrammarBuilder Named Constr) ->
      union g g `shouldBe` g

    prop "should be an upper bound: G1 ⊆ G1 ∪ G2" $ \(g1 :: GrammarBuilder Named Constr) (g2 :: GrammarBuilder Named Constr) ->
      g1 `shouldBeSubsetOf` union g1 g2


  -- describe "Intersection" $ do
  --   it "of a subset of the PCF grammar should be that subset" $
  --     intersection pcf pcf_sub `shouldBeLiteral` (grammar "PStart⨯PSStart" $
  --                                                 M.fromList [ ("Exp⨯Exp", [ Ctor "Zero" []
  --                                                                          , Ctor "Succ" ["Exp⨯Exp"]
  --                                                                          , Ctor "Pred" ["Exp⨯Exp"]])
  --                                                            , ("PStart⨯PSStart", [ Ctor "Zero" []
  --                                                                                 , Ctor "Succ" ["Exp⨯Exp"]
  --                                                                                 , Ctor "Pred" ["Exp⨯Exp"]
  --                                                                                 , Ctor "Num" []
  --                                                                                 , Ctor "Fun" [ "Type⨯Type", "Type⨯Type" ]])
  --                                                            , ("Type⨯Type", [ Ctor "Num" []
  --                                                                            , Ctor "Fun" [ "Type⨯Type", "Type⨯Type" ]])])

  --   it "should give an empty grammar if the arguments have no intersection" $ do
  --     intersection nondet pcf `shouldBeLiteral` (grammar "S⨯PStart" M.empty)

  --   it "should give an empty grammar when one of the arguments is an empty grammar" $ do
  --     intersection nondet infinite `shouldBeLiteral` (grammar "S⨯EStart" M.empty)
  --     intersection infinite nondet `shouldBeLiteral` (grammar "EStart⨯S" M.empty)

  describe "Inclusion" $ do
    it "should work for non-deterministic grammars" $ do
      let g :: GrammarBuilder Named Constr
          g = grammar "S" [ ("S", [ ("f",["A", "B"])
                                  , ("f",["A'", "B'"])])
                          , ("A", [ ("a",[]) ])
                          , ("B", [ ("b",[]) ])
                          , ("A'", [ ("a'",[]) ])
                          , ("B'", [ ("b'",[]) ])
                          ]
                          []
          g' :: GrammarBuilder Named Constr
          g' = grammar "S" [ ("S", [("f",["A", "B"])])
                           , ("A", [("a",[]), ("a'",[])])
                           , ("B", [("b",[]), ("b'",[])])
                           ]
                           []
      g `shouldBeSubsetOf` g'
      g' `shouldNotBeSubsetOf` g

    it "should work for recursive grammars" $ do
      pcf_sub `shouldBeSubsetOf` pcf
      pcf `shouldNotBeSubsetOf` pcf_sub

    prop "should be reflexive" $ \(g :: GrammarBuilder Named Constr) ->
      g `shouldBeSubsetOf` g

  describe "Grammar Optimizations" $ do
    describe "Epsilon Closure" $ do
      prop "should describe the same language: epsilonClosure g = g" $
        \(g :: GrammarBuilder Named Constr) -> epsilonClosure g `shouldBe` g

    describe "drop unreachable prductions" $ do
      prop "should describe the same language: dropUnreachable g = g" $
        \(g :: GrammarBuilder Named Constr) -> dropUnreachable g `shouldBe` g

    describe "drop unproductive prductions" $ do
      prop "should describe the same language: dropUnproductive g = g" $
        \(g :: GrammarBuilder Named Constr) -> do
           m <- try (dropUnreachable (dropUnproductive g) `shouldBe` g)
           case m of
             Left (_ :: ErrorCall) -> 
               expectationFailure (printf "g = %s\ndropUnproductive g = %s" (show g) (show (dropUnproductive (dropUnproductive g))))
             Right _ -> return ()

  -- describe "Alphabet" $ do
  --   it "should correctly list the alphabet of PCF" $
  --     let a = M.fromList [("App", [2]), ("Abs", [3]), ("Zero", [0]), ("Succ", [1]), ("Pred", [1]), ("Ifz", [3]), ("Num", [0]), ("Fun", [2]), ("String", [0])]
  --     in alphabet pcf `shouldBe` a

  -- describe "Normalization" $ do
  --   it "should work on an empty grammar" $ do
  --     let empty :: GrammarBuilder Text
  --         empty = grammar "S" $ M.fromList [ ("S", []) ]
  --     dropUnreachable empty `shouldBeLiteral` empty
  --     dropEmpty empty `shouldBeLiteral` grammar "S" M.empty
  --     normalize empty `shouldBeLiteral` grammar "S" M.empty

  -- describe "Determinization" $ do
  --   it "should work on an empty grammar" $ do
  --     let empty :: GrammarBuilder Text
  --         empty = grammar "S" $ M.fromList [ ("S", []) ]
  --     empty `shouldSatisfy` isDeterministic
  --     determinize empty `shouldBe` empty

  --   it "should correctly determinize PCF" $ do
  --     let det = determinize pcf
  --     det `shouldSatisfy` isDeterministic
  --     det `shouldBe` pcf
  --     determinize det `shouldBe` pcf

  --   it "should correctly determinize the nondeterministic grammar" $ do
  --     let det = determinize nondet
  --     nondet `shouldNotSatisfy` isDeterministic
  --     nondet' `shouldNotSatisfy` isDeterministic
  --     det `shouldSatisfy` isDeterministic
  --     det `shouldBe` nondet

  --   it "should correctly determinize another nondeterministic grammar" $ do
  --     let ng :: GrammarBuilder Text
  --         ng = grammar "S" $ M.fromList [ ("S", [ Ctor "foo" [], Ctor "foo" [] ]) ]
  --         det = determinize ng
  --     ng `shouldNotSatisfy` isDeterministic
  --     det `shouldSatisfy` isDeterministic
  --     det `shouldBe` ng

  --   it "should correctly determinize another nondeterministic grammar" $ do
  --     let ng :: GrammarBuilder Text
  --         ng = grammar "S" $ M.fromList [ ("S", [ Ctor "foo" [ "A", "B" ] ])
  --                                       , ("A", [ Ctor "bar" [ "C" ]
  --                                               , Ctor "bar" [ "D" ]])
  --                                       , ("B", [ Ctor "baz" [ "E" ]
  --                                               , Ctor "baz" [ "F" ]])
  --                                       , ("C", [ Ctor "c" [] ])
  --                                       , ("D", [ Ctor "d" [] ])
  --                                       , ("E", [ Ctor "e" [] ])
  --                                       , ("F", [ Ctor "f" [] ])]
  --         det = determinize ng
  --     ng `shouldNotSatisfy` isDeterministic
  --     det `shouldSatisfy` isDeterministic
  --     det `shouldBe` ng

  --   it "should correctly determinize the infinite grammar" $ do
  --     let det = determinize infinite
  --     det `shouldSatisfy` isDeterministic
  --     det `shouldBe` infinite

  -- describe "Widening" $ do
  --   it "wideMap should compute the depths and principal label sets of nonterminals in PCF" $ do
  --     let pcf' = evalState pcf 0
  --         pcf_wideMap = wideMap pcf'
  --         pcf_prods = productions pcf'
  --     M.lookup "PStart" pcf_wideMap `shouldBe` Just (0,S.empty,pcf_prods M.! "PStart")
  --     M.lookup "Exp" pcf_wideMap `shouldBe` Just (1,S.fromList ["App","Abs","Zero","Succ","Pred","Ifz"],pcf_prods M.! "Exp")
  --     M.lookup "String" pcf_wideMap `shouldBe` Just (2,S.singleton "String",pcf_prods M.! "String")
  --     M.lookup "Type" pcf_wideMap `shouldBe` Just (1,S.fromList ["Num","Fun"],pcf_prods M.! "Type")

  --   it "wideMap should compute the depths and principal label sets of nonterminals in the nondeterministic grammar" $ do
  --     let nondet'' = evalState nondet' 0
  --         nondet_wideMap = wideMap nondet''
  --         nondet_prods = productions nondet''
  --     M.lookup "S" nondet_wideMap `shouldBe` Just (0,S.empty,nondet_prods M.! "S")
  --     M.lookup "F" nondet_wideMap `shouldBe` Just (1,S.singleton "f",nondet_prods M.! "F")
  --     M.lookup "G" nondet_wideMap `shouldBe` Just (2,S.singleton "g",nondet_prods M.! "G")
  --     M.lookup "H" nondet_wideMap `shouldBe` Just (2,S.empty,nondet_prods M.! "H")
  --     M.lookup "A" nondet_wideMap `shouldBe` Just (3,S.singleton "a",nondet_prods M.! "A")

  --   it "should build a correspondence set on the example from the paper" $ do
  --     let cons0' = evalState (epsilonClosure cons0) 0
  --         cons1' = evalState (epsilonClosure cons1) 0
  --         cons_w0 = wideMap cons0'
  --         cons_w1 = wideMap cons1'
  --     correspondenceSet (start cons0') cons_w0 (start cons1') cons_w1 `shouldBe` M.fromList [(("T0","T3"),S.empty)
  --                                                                                           ,(("T1","T4"),S.singleton ("cons","T3",0))
  --                                                                                           ,(("T2","T5"),S.singleton ("cons","T3",1))]

  --   it "should build a correspondence set on the PCF grammar " $ do
  --     let pcf_sub' = evalState (epsilonClosure pcf_sub) 0
  --         pcf' = evalState (epsilonClosure pcf) 0
  --         pcf_sub_w = wideMap pcf_sub'
  --         pcf_w = wideMap pcf'
  --     correspondenceSet (start pcf_sub') pcf_sub_w (start pcf') pcf_w `shouldBe` M.fromList [(("PSStart","PStart"),S.empty)]

  --   it "should build a correspondence set on the arithmetic example from the paper" $ do
  --     let arith0' = evalState (epsilonClosure arith0) 0
  --         arith1' = evalState (epsilonClosure arith1) 0
  --         arith_w0 = wideMap arith0'
  --         arith_w1 = wideMap arith1'
  --     correspondenceSet (start arith0') arith_w0 (start arith1') arith_w1 `shouldBe` M.fromList [(("T0","Tn"),S.empty)
  --                                                                                               ,(("Tx","T3"),S.fromList [("Add","Tn",0)
  --                                                                                                                        ,("par","T7",0)])
  --                                                                                               ,(("T1","T6"),S.fromList [("Add","Tn",1)
  --                                                                                                                        ,("Mul","T6",0)])
  --                                                                                               ,(("T2","T7"),S.singleton ("Mul","T6",1))]

  --   it "should find a set of widening topological clashes on the example from the paper" $ do
  --     let cons0' = evalState (epsilonClosure cons0) 0
  --         cons1' = evalState (epsilonClosure cons1) 0
  --         cons_w0 = wideMap cons0'
  --         cons_w1 = wideMap cons1'
  --         corr = correspondenceSet (start cons0') cons_w0 (start cons1') cons_w1
  --     wideningClashes corr cons_w0 cons_w1 `shouldBe` M.fromList [(("T2","T5"),S.singleton ("cons","T3",1))]

  --   it "should find a set of widening topological clashes on the PCF grammar" $ do
  --     let pcf_sub' = evalState (epsilonClosure pcf_sub) 0
  --         pcf' = evalState (epsilonClosure pcf) 0
  --         pcf_sub_w = wideMap pcf_sub'
  --         pcf_w = wideMap pcf'
  --         corr = correspondenceSet (start pcf_sub') pcf_sub_w (start pcf') pcf_w
  --     wideningClashes corr pcf_sub_w pcf_w `shouldBe` M.fromList [(("PSStart","PStart"),S.empty)]

  --   it "should find a set of widening topological clashes on the arithmetic example from the paper" $ do
  --     let arith0' = evalState (epsilonClosure arith0) 0
  --         arith1' = evalState (epsilonClosure arith1) 0
  --         arith_w0 = wideMap arith0'
  --         arith_w1 = wideMap arith1'
  --         corr = correspondenceSet (start arith0') arith_w0 (start arith1') arith_w1
  --     wideningClashes corr arith_w0 arith_w1 `shouldBe` M.fromList [(("Tx","T3"),S.fromList [("Add","Tn",0)
  --                                                                                           ,("par","T7",0)])]

  --   it "should find ancestors for the example from the paper" $ do
  --     let cons1' = evalState cons1 0
  --         w = wideMap cons1'
  --     findAncestors "T5" w cons1' `shouldBe` ["T3"]

  --   it "should find ancestors for the arithmetic example from the paper" $ do
  --     let arith1' = evalState arith1 0
  --         w = wideMap arith1'
  --     findAncestors "T3" w arith1' `shouldBe` ["T6","T7","Tn"]

  --   it "should find ancestors for PCF" $ do
  --     let pcf' = evalState pcf 0
  --         w = wideMap pcf'
  --     findAncestors "PStart" w pcf' `shouldBe` []
  --     findAncestors "Exp" w pcf' `shouldBe` ["PStart"]
  --     findAncestors "String" w pcf' `shouldBe` ["Exp","PStart"]
  --     findAncestors "Type" w pcf' `shouldBe` ["Exp","PStart"]

  --   it "should find ancestors for the nondeterministic grammar" $ do
  --     let nondet'' = evalState nondet' 0
  --         w = wideMap nondet''
  --     findAncestors "G" w nondet'' `shouldBe` ["F", "H", "S"]
  --     findAncestors "A" w nondet'' `shouldBe` ["F", "G", "H", "S"]

  --   it "should find the best arc ancestor for the example from the paper" $ do
  --     let cons0' = evalState (epsilonClosure cons0) 0
  --         cons1' = evalState (epsilonClosure cons1) 0
  --         w0 = wideMap cons0'
  --         w1 = wideMap cons1'
  --         ancs = findAncestors "T5" w1 cons1'
  --     arcAncestor "T2" "T5" ancs w0 w1 cons1' `shouldBe` Just "T3"

  --   it "should find the best arc ancestor for the arithmetic example from the paper" $ do
  --     let arith0' = evalState (epsilonClosure arith0) 0
  --         arith1' = evalState (epsilonClosure arith1) 0
  --         w0 = wideMap arith0'
  --         w1 = wideMap arith1'
  --         ancs = findAncestors "T3" w1 arith1'
  --     arcAncestor "Tx" "T3" ancs w0 w1 arith1' `shouldBe` Just "Tn"

  --   it "should find the best arc ancestor for PCF" $ do
  --     let pcf' = evalState (epsilonClosure pcf) 0
  --         w1 = wideMap pcf'
  --     arcAncestor "PSStart" "PStart" (findAncestors "PStart" w1 pcf') w1 w1 pcf' `shouldBe` Nothing
  --     arcAncestor "Exp" "Exp" (findAncestors "Exp" w1 pcf') w1 w1 pcf' `shouldBe` Just "PStart"
  --     arcAncestor "String" "String" (findAncestors "String" w1 pcf') w1 w1 pcf' `shouldBe` Nothing
  --     arcAncestor "Type" "Type" (findAncestors "Type" w1 pcf') w1 w1 pcf' `shouldBe` Just "PStart"

  --   it "should find a set of arc replacements for the widening topological clashes for the example from the paper" $ do
  --     let cons0' = evalState (epsilonClosure cons0) 0
  --         cons1' = evalState (epsilonClosure cons1) 0
  --         w0 = wideMap cons0'
  --         w1 = wideMap cons1'
  --         corr = correspondenceSet (start cons0') w0 (start cons1') w1
  --         wideClashes01 = wideningClashes corr w0 w1
  --     arcReplacements cons1' wideClashes01 w0 w1 `shouldBe` M.fromList [(("T5","T3"),S.singleton ("cons","T3",1))]

  --   it "should find a set of arc replacements for the widening topological clashes for the PCF grammar" $ do
  --     let pcf_sub' = evalState (epsilonClosure pcf_sub) 0
  --         pcf' = evalState (epsilonClosure pcf) 0
  --         w0 = wideMap pcf_sub'
  --         w1 = wideMap pcf'
  --         corr = correspondenceSet (start pcf_sub') w0 (start pcf') w1
  --         wideClashes = wideningClashes corr w0 w1
  --     arcReplacements pcf' wideClashes w0 w1 `shouldBe` M.fromList []

  --   it "should find a set of arc replacements for the widening topological clashes for the arithmetic example from the paper " $ do
  --     let arith0' = evalState (epsilonClosure arith0) 0
  --         arith1' = evalState (epsilonClosure arith1) 0
  --         w0 = wideMap arith0'
  --         w1 = wideMap arith1'
  --         corr = correspondenceSet (start arith0') w0 (start arith1') w1
  --         wideClashes = wideningClashes corr w0 w1
  --     arcReplacements arith1' wideClashes w0 w1 `shouldBe` M.fromList [(("T3","Tn"),S.fromList [("Add","Tn",0)
  --                                                                                              ,("par","T7",0)])]

  --   it "should replace nonterminals with ancestors" $ do
  --     let consr :: GrammarBuilder Int Constr
  --         consr = grammar "T3" $ M.fromList [ ("T3", [ Ctor "nil" [], Ctor "cons" ["T4","T3"] ])
  --                                           , ("T4", [ Ctor "any" [] ])
  --                                           , ("T6", [ Ctor "any" [] ])
  --                                           , ("T7", [ Ctor "nil" [] ])]
  --         cons1' = evalState (epsilonClosure cons1) 0
  --     return (replaceNonterm "T5" "T3" cons1') `shouldBeLiteral` consr

  --   it "should replace an edge" $ do
  --     let consr :: GrammarBuilder Int Constr
  --         consr = grammar "T3" $ M.fromList [ ("T3", [ Ctor "nil" [], Ctor "cons" ["T4","T3"] ])
  --                                           , ("T4", [ Ctor "any" [] ])
  --                                           , ("T5", [ Ctor "nil" [], Ctor "cons" ["T6","T7"] ])
  --                                           , ("T6", [ Ctor "any" [] ])
  --                                           , ("T7", [ Ctor "nil" [] ])]
  --         cons1' = evalState (epsilonClosure cons1) 0
  --     return (replaceEdge "cons" "T3" 1 "T3" cons1') `shouldBeLiteral` consr

  --   it "should work on the examples from the paper" $ do
  --     widen' cons0 cons1 `shouldBeLiteral` cons01
  --     widen' cons1 cons2 `shouldBeLiteral` cons12
  --     widen' arith0 arith1 `shouldBe` arith01
  --     widen' arith1 (widen' arith0 arith1) `shouldBeLiteral` arith01
  --     widen' arith2 arith3 `shouldBeLiteral` arith3

  --   it "should be an upper bound" $ do
  --     let w_cons = widen' cons0 cons1
  --         w_pcf = widen' pcf_sub pcf
  --         w_arith = widen' arith0 arith1
  --     pcf `shouldSatisfy` (`subsetOf` w_pcf)
  --     pcf_sub `shouldSatisfy` (`subsetOf` w_pcf)
  --     cons0 `shouldSatisfy` subsetOf w_cons
  --     cons1 `shouldSatisfy` subsetOf w_cons
  --     arith0 `shouldSatisfy` subsetOf w_arith
  --     arith1 `shouldSatisfy` subsetOf w_arith

  where
    nondet :: GrammarBuilder Named Constr
    nondet = grammar "S" [ ("A", [ ("a",[]) ])
                         , ("G", [ ("g",[ "G" ])
                                 , ("g",[ "A" ])])
                         , ("F", [ ("f",[ "G", "G" ]) ])
                         ]
                         [ ("S", [ "F" ])]
    -- nondet' = grammar "S" $ [ ("S", [ Eps "F" ])
    --                         , ("A", [ Ctor "a" [] ])
    --                         , ("G", [ Ctor "g" [ "G" ]
    --                                 , Ctor "g" [ "A" ]])
    --                         , ("H", [ Eps "G" ])
    --                         , ("F", [ Ctor "f" [ "G", "H" ]])]
    -- infinite = grammar "EStart" $ [ ("EStart", [ Ctor "Bar" ["EStart"]])]
    pcf :: GrammarBuilder Named Constr
    pcf = grammar "PStart" [ ("Exp", [ ("App",["Exp", "Exp"])
                                     , ("Abs",["String", "Type", "Exp"])
                                     , ("Zero",[])
                                     , ("Succ",["Exp"])
                                     , ("Pred",["Exp"])
                                     , ("Ifz",["Exp", "Exp", "Exp"])
                                     ])
                           , ("Type", [ ("Num",[])
                                      , ("Fun",["Type", "Type"])
                                      ])
                           , ("String", [ ("String",[]) ])
                           ]

                           [ ("PStart", [ "Exp" , "Type" ]) ]
    pcf_sub :: GrammarBuilder Named Constr
    pcf_sub = grammar "PSStart" [ ("Exp", [ ("Succ",[ "Exp" ])
                                          , ("Pred",[ "Exp" ])
                                          , ("Zero",[])])
                                , ("Type", [ ("Num",[])
                                           , ("Fun",["Type", "Type"])])]
                                [ ("PSStart", [ "Exp" , "Type" ]) ]
    pcf_nondet :: GrammarBuilder Named Constr
    pcf_nondet = grammar "Start" [ ("A", [ ("a",[]) ])
                                 , ("G", [ ("g",[ "G" ])
                                         , ("g",[ "A" ])])
                                 , ("F", [ ("f",[ "G", "G" ])])
                                 , ("Exp", [ ("App",["Exp","Exp"])
                                           , ("Abs",["String", "Type", "Exp"])
                                           , ("Zero",[])
                                           , ("Succ",["Exp"])
                                           , ("Pred",["Exp"])
                                           , ("Ifz",["Exp", "Exp", "Exp"])])
                                 , ("Type", [ ("Num",[])
                                            , ("Fun",["Type","Type"])])
                                 , ("String", [ ("String",[]) ])]

                                 [ ("Start", [ "Exp" , "Type", "F" ]) ] 

    -- cons0 :: GrammarBuilder Named Constr
    -- cons0 = grammar "T0" $ M.fromList [ ("T0", [ Ctor "nil" [], Ctor "cons" ["T1","T2"] ])
    --                                   , ("T1", [ Ctor "any" [] ])
    --                                   , ("T2", [ Ctor "nil" [] ])]
    -- cons1 :: GrammarBuilder Named Constr
    -- cons1 = grammar "T3" $ M.fromList [ ("T3", [ Ctor "nil" [], Ctor "cons" ["T4","T5"] ])
    --                                   , ("T4", [ Ctor "any" [] ])
    --                                   , ("T5", [ Ctor "nil" [], Ctor "cons" ["T6","T7"] ])
    --                                   , ("T6", [ Ctor "any" [] ])
    --                                   , ("T7", [ Ctor "nil" [] ])]
    -- cons2 :: GrammarBuilder Named Constr
    -- cons2 = grammar "T8" $ M.fromList [ ("T8", [ Ctor "nil" [], Ctor "cons" ["T9","T10"] ])
    --                                   , ("T9", [ Ctor "any" [] ])
    --                                   , ("T10", [ Ctor "nil" [], Ctor "cons" ["T11","T12"] ])
    --                                   , ("T11", [ Ctor "any" [] ])
    --                                   , ("T12", [ Ctor "nil" [], Ctor "cons" ["T13","T14"] ])
    --                                   , ("T13", [ Ctor "any" [] ])
    --                                   , ("T14", [ Ctor "nil" [] ])]
    -- cons01 :: GrammarBuilder Named Constr
    -- cons01 = grammar "T3" $ M.fromList [ ("T3", [ Ctor "nil" [], Ctor "cons" ["T4", "T3"] ])
    --                                    , ("T4", [ Ctor "any" [] ])]
    -- cons12 :: GrammarBuilder Named Constr
    -- cons12 = grammar "T8" $ M.fromList [ ("T8", [ Ctor "nil" [], Ctor "cons" ["T9", "T10"] ])
    --                                    , ("T9", [ Ctor "any" [] ])
    --                                    , ("T10", [ Ctor "nil" [], Ctor "cons" ["T11", "T10"] ])
    --                                    , ("T11", [ Ctor "any" [] ])]

    -- arith0 :: GrammarBuilder Named Constr
    -- arith0 = grammar "T0" $ M.fromList [ ("T0", [ Ctor "zero" [], Ctor "Add" ["Tx", "T1"] ])
    --                                    , ("Tx", [ Ctor "zero" [] ])
    --                                    , ("T1", [ Ctor "one" [], Ctor "Mul" ["T1","T2"] ])
    --                                    , ("T2", [ Ctor "cst" [], Ctor "par" ["Tx"], Ctor "var" [] ])]
    -- arith1 :: GrammarBuilder Named Constr
    -- arith1 = grammar "Tn" $ M.fromList [ ("Tn", [ Ctor "zero" [], Ctor "Add" ["T3","T6"] ])
    --                                    , ("T3", [ Ctor "zero" [], Ctor "Add" ["Tx","T4"] ])
    --                                    , ("Tx", [ Ctor "Zero" [] ])
    --                                    , ("T4", [ Ctor "one" [], Ctor "Mul" ["T4","T5"] ])
    --                                    , ("T5", [ Ctor "cst" [], Ctor "par" ["Tx"], Ctor "var" [] ])
    --                                    , ("T6", [ Ctor "one" [], Ctor "Mul" ["T6","T7"] ])
    --                                    , ("T7", [ Ctor "cst" [], Ctor "par" ["T3"], Ctor "var" [] ])]
    -- arith2 :: GrammarBuilder Named Constr
    -- arith2 = grammar "T0" $ M.fromList [ ("T0", [ Ctor "cst" [], Ctor "var" [] ]) ]
    -- arith3 :: GrammarBuilder Named Constr
    -- arith3 = grammar "Tn" $ M.fromList [ ("Tn", [ Ctor "cst" [], Ctor "par" ["Tx"], Ctor "var" [] ])
    --                                    , ("Tx", [ Ctor "zero" [] ]) ]
    -- arith01 :: GrammarBuilder Named Constr
    -- arith01 = grammar "Tn" $ M.fromList [ ("Tn", [ Ctor "zero" [], Ctor "Add" ["Tn","T6"] ])
    --                                     , ("T6", [ Ctor "one" [], Ctor "Mul" ["T6","T7"] ])
    --                                     , ("T7", [ Ctor "var" [], Ctor "par" ["Tn"], Ctor "cst" [] ])]

    shouldBeSubsetOf :: (Show n, Show (t n), IsGrammar n t) => GrammarBuilder n t -> GrammarBuilder n t -> Expectation
    shouldBeSubsetOf b1 b2 = unless (b1 `subsetOf'` b2) $
      expectationFailure (printf "Grammar %s is not subset of %s" (show b1) (show b2))

    shouldNotBeSubsetOf :: (Show n, Show (t n), IsGrammar n t) => GrammarBuilder n t -> GrammarBuilder n t -> Expectation
    shouldNotBeSubsetOf b1 b2 = when (b1 `subsetOf'` b2) $
      expectationFailure (printf "Grammar %s is subset of %s" (show b1) (show b2))
                        

type NonTerminals = [String]
type Alphabet = [(String,Int)]

instance Arbitrary (GrammarBuilder Named Constr) where
  arbitrary = arbitraryGrammar
              ["A","B","C","D","E","F"]
              [("a",0),("b",0),("c",0),("f",1),("g",2),("h",0),("h",1),("h",2)]

arbitraryGrammar :: NonTerminals -> Alphabet -> Gen (GrammarBuilder Named Constr)
arbitraryGrammar ns alph = do
  grammar <$> elements ns <*> genCons <*> genEps
  where

    genCons :: Gen [(String,Constr String)]
    genCons = forM ns $ \n -> do
      constrs <- listRange 1 3 (elements alph)
      cs <- forM constrs $ \(con,arity) -> do
        ts <- vectorOf arity (elements ns)
        return (con,ts)
      return (n,fromList cs)

    genEps :: Gen [(String,[String])]
    genEps = do
      dom <- listRange 0 2 (elements ns)
      forM dom $ \x -> do
        cod <- listRange 1 2 (elements ns)
        return (x,cod)


    listRange :: Int -> Int -> Gen a -> Gen [a]
    listRange n m xs = do
      i <- choose (n,m)
      vectorOf i xs
