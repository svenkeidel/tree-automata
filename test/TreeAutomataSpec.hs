{-# LANGUAGE OverloadedStrings #-}
module TreeAutomataSpec(main, spec) where

import           Control.Monad
import           Control.Monad.State hiding (sequence)

import qualified Data.Map as M
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
      isDeterministic pcf' `shouldBe` True
      pcf' `shouldBe` pcf

    it "should destruct and rebuild a nondeterministic grammar" $ do
      let nondet'' = fromSubterms (toSubterms nondet)
      isDeterministic nondet'' `shouldBe` False
      nondet'' `shouldBe` nondet

    it "should destruct and rebuild the infinite grammar into the empty grammar" $ do
      isEmpty (fromSubterms (toSubterms infinite)) `shouldBe` True

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
      isEmpty infinite `shouldBe` True

    it "should be false on the nondeterministic grammar" $
      isEmpty nondet `shouldBe` False

    it "should be false on the PCF grammar" $
      isEmpty pcf `shouldBe` False

    it "should be false on the subset of PCF" $
      isEmpty pcf_sub `shouldBe` False

  describe "Singletoness" $ do
    it "should be false on the infinite infinite grammar" $
      isSingleton infinite `shouldBe` False

    it "should be false on the nondeterministic grammar" $
      isSingleton nondet `shouldBe` False

    it "should be false on the PCF grammar" $
      isSingleton pcf `shouldBe` False

    it "should be true on a singleton grammar" $
      let g = grammar "Foo" (M.fromList [ ("Foo", [ Ctor ("Bar"::Text) [ "Baz" ] ])
                                        , ("Baz", [ Ctor ("Baz"::Text) [] ]) ])
      in isSingleton g `shouldBe` True

  describe "Union" $ do
    it "should work on the union of two small grammars" $
      let g1 :: GrammarBuilder Text
          g1 = grammar "Foo" $ M.fromList [ ("Foo", [ Eps "Exp" ])
                                          , ("Exp", [ Ctor "Zero" [] ])]
          g2 :: GrammarBuilder Text
          g2 = grammar "Bar" $ M.fromList [ ("Bar", [ Eps "Type" ])
                                          , ("Type", [ Ctor "Num" [] ])]
          g3 :: GrammarBuilder Text
          g3 = grammar "Start0" $ M.fromList [ ("Start0", [ Eps "Foo", Eps "Bar" ])
                                             , ("Bar", [ Eps "Type" ])
                                             , ("Exp", [ Ctor "Zero" [] ])
                                             , ("Foo", [ Eps "Exp" ])
                                             , ("Type", [ Ctor "Num" [] ])]
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
      let g = grammar "S" $ M.fromList [("S", [ Ctor "f" ["A"]
                                              , Ctor "c" []
                                              , Ctor "f" ["B"]])
                                       ,("A", [ Ctor "g" ["S"]
                                              , Ctor "e" []])
                                       ,("B", [ Ctor "b" []])]
          g' = grammar "S'" $ M.fromList [("S'", [ Ctor "f" ["A'"]
                                                 , Ctor "c" []
                                                 , Ctor "f" ["B'"]])
                                         ,("A'", [ Ctor "g" ["S'"]
                                                 , Ctor "e" []])
                                         ,("B'", [ Ctor "b" []])]
      in (g::GrammarBuilder Text) `subsetOf` (g'::GrammarBuilder Text) `shouldBe` True

    it "should be true for the PCF grammar and a subset of the PCF grammar" $
      pcf_sub `subsetOf` pcf `shouldBe` True

    it "should not work when the arguments are inverted" $
      pcf `subsetOf` pcf_sub `shouldBe` False

    it "reflexivity should hold on PCF" $
      pcf `subsetOf` pcf `shouldBe` True

    it "reflexivity should hold on the nondeterministic grammar" $
      nondet `subsetOf` nondet `shouldBe` True

    it "should not hold for languages that do not intersect" $ do
      nondet `subsetOf` pcf `shouldBe` False
      pcf `subsetOf` nondet `shouldBe` False

    it "should hold for equal grammars" $ do
      pcf `subsetOf` pcf `shouldBe` True
      nondet `subsetOf` nondet `shouldBe` True

    it "should work for a nondeterministic grammar" $
      let det = grammar "Nt0" $ M.fromList [ ("Nt0", [ Ctor "f" ["Nt1","Nt1"]])
                                           , ("Nt1", [ Ctor "g" ["Nt2"]])
                                           , ("Nt2", [ Ctor "a" [], Ctor "g" ["Nt2"]])]
      in det `subsetOf` nondet `shouldBe` True

  describe "Equality" $ do
    it "should be true when comparing the same grammar" $ do
      pcf == pcf `shouldBe` True
      pcf `shouldBe` pcf

    it "should be true when comparing the same grammar (nondet)" $ do
      nondet == nondet `shouldBe` True
      nondet `shouldBe` nondet

    it "should be false when comparing different grammars" $ do
      pcf == nondet `shouldBe` False
      pcf `shouldNotBe` nondet

    it "should be true when comparing different grammars producing the same language" $ do
      nondet == nondet' `shouldBe` True
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

  describe "Determinization" $ do
    it "should correctly determinize PCF" $ do
      let det = determinize pcf
      isDeterministic det `shouldBe` True
      det `shouldBe` pcf
      determinize det `shouldBe` pcf

    it "should correctly determinize the nondeterministic grammar" $ do
      let det = determinize nondet
      isDeterministic nondet `shouldBe` False
      isDeterministic det `shouldBe` True
      det `shouldBe` nondet

    it "should correctly determinize another nondeterministic grammar" $ do
      let ng :: GrammarBuilder Text
          ng = grammar "S" $ M.fromList [ ("S", [ Ctor "foo" [], Ctor "foo" [] ]) ]
          det = determinize ng
      isDeterministic ng `shouldBe` False
      isDeterministic det `shouldBe` True
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
      isDeterministic ng `shouldBe` False
      isDeterministic det `shouldBe` True
      det `shouldBe` ng

    it "should correctly determinize the infinite grammar" $ do
      let det = determinize infinite
      isDeterministic det `shouldBe` True
      det `shouldBe` infinite

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
      -- TODO: apparently the order of the right hand sides in the maps matters. For now, just make the right order in the test cases,
      -- but eventually we should implement a custom equality check that does not depend on order.
        unless (start actual' == start expected' && productions actual' == productions expected')
          (assertFailure $ "Grammars are not literally equal.\nExpected:\n\n" ++ show expected ++ "\nbut got:\n\n" ++ show actual)
        where
          expected' = evalState expected 0
          actual' = evalState actual 0
