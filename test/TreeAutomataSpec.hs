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
    it "should destruct and rebuild PCF" $
      pendingWith "infinite"
      -- fromSubterms (toSubterms pcf) `shouldBe` pcf

    it "should destruct and rebuild simple" $
      fromSubterms (toSubterms simple) `shouldBe` simple

    it "should destruct and rebuild the empty grammar" $
      fromSubterms (toSubterms (empty::GrammarBuilder Text)) `shouldBe` empty

    it "should destruct and rebuild the infinite grammar into the empty grammar" $ do
      fromSubterms (toSubterms infinite) `shouldBe` empty

  describe "Size" $ do
    it "should be 25 on PCF" $
      size pcf `shouldBe` 25

    it "should be 10 on simple" $
      size simple `shouldBe` 10

    it "should be 0 on the empty grammar" $
      size empty `shouldBe` 0

    it "should be defined on an infinite grammar" $
      size infinite `shouldBe` 2

  describe "Height" $ do
    it "should be 11 on PCF" $
      height pcf `shouldBe` 11

    it "should be 5 on simple" $
      height simple `shouldBe` 5

    it "should be 0 on the empty grammar" $
      height empty `shouldBe` 0

    it "should be defined on an infinite grammar" $
      height infinite `shouldBe` 1

  describe "Productivity" $ do
    it "should give all nonterminals for PCF" $ do
      let pcf' = evalState pcf 0
      map (`isProductive` pcf') ["Exp", "Type", "String", "PStart"] `shouldBe` [True, True, True, True]

    it "should give no nonterminals for infinite" $ do
      let infinite' = evalState infinite 0
      map (`isProductive` infinite') ["foo", "EStart"] `shouldBe` [False, False]

    it "should give all nonterminals for simple" $ do
      let simple'' = evalState simple 0
      map (`isProductive` simple'') ["S", "A", "G", "F"] `shouldBe` [True, True, True, True]

    it "should give all nonterminals for simple'" $ do
      let simple''' = evalState simple' 0
      map (`isProductive` simple''') ["S", "A", "G", "H", "F"] `shouldBe` [True, True, True, True, True]

    it "should give all nonterminals for the PCF subset" $ do
      let pcf_sub' = evalState pcf_sub 0
      map (`isProductive` pcf_sub') ["PSStart", "Exp", "Type"] `shouldBe` [True, True, True]

    it "should give all nonterminals for the union of PCF and simple" $ do
      let pcf_simple' = evalState pcf_simple 0
      map (`isProductive` pcf_simple') ["Nt0", "Nt1", "Nt2", "Nt3", "Nt4", "Nt5"] `shouldBe` [True, True, True, True, True, True]

    it "should correctly compute that PCF produces Zero, Num and String" $
      map (\n -> produces (pcf::GrammarBuilder Text) n) ["Zero", "Num", "String", "Succ", "Pred", "Ifz"] `shouldBe` [True, True, True, False, False, False]

    it "should correctly compute that the infinite grammar does not produce \"foo\"" $
      produces infinite "foo" `shouldBe` False

  describe "Emptiness" $ do
    it "should be true on the empty grammar" $
      isEmpty empty `shouldBe` True

    it "should be true on the infinite infinite grammar" $
      isEmpty infinite `shouldBe` True

    it "should be false on the simple grammar" $
      isEmpty simple `shouldBe` False

    it "should be false on the PCF grammar" $
      isEmpty pcf `shouldBe` False

    it "should be false on the subset of PCF" $
      isEmpty pcf_sub `shouldBe` False

  describe "Singletoness" $ do
    it "should be false on the empty grammar" $
      isSingleton TreeAutomata.empty `shouldBe` False

    it "should be false on the infinite infinite grammar" $
      isSingleton infinite `shouldBe` False

    it "should be false on the simple grammar" $
      isSingleton simple `shouldBe` False

    it "should be false on the PCF grammar" $
      isSingleton pcf `shouldBe` False

    it "should be true on a singleton grammar" $
      let g = grammar "Foo" (M.fromList [ ("Foo", [ Ctor ("Bar"::Text) [ "Baz" ] ])
                                        , ("Baz", [ Ctor ("Baz"::Text) [] ]) ])
      in isSingleton g `shouldBe` True

  describe "Union" $ do
    it "should work on the union of two small grammars" $
      let g1 = grammar "Foo" $ M.fromList [ ("Foo", [ Eps "Exp" ])
                                          , ("Exp", [ Ctor "Zero" [] ])]
          g2 = grammar "Bar" $ M.fromList [ ("Bar", [ Eps "Type" ])
                                          , ("Type", [ Ctor "Num" [] ])]
          g3 = grammar "Nt0" $ M.fromList [ ("Nt0", [ Ctor "Zero" []
                                                    , Ctor "Num" [] ])]
      in union (g1::GrammarBuilder Text) (g2::GrammarBuilder Text) `shouldBeLiteral` (g3::GrammarBuilder Text)

    it "should work on the union of the simple and PCF grammars" $
      union pcf simple `shouldBeLiteral` pcf_simple

    it "should work on the union of the infinite and empty grammars" $
      union infinite empty `shouldBeLiteral` empty

    it "should produce the same language when taken over identical grammars (PCF)" $ do
      union pcf pcf `shouldBe` pcf

    it "should produce the same language when taken over identical grammars (simple)" $ do
      union simple simple `shouldBe` simple

    it "the list version should work on an empty list" $
      (union' []::GrammarBuilder Text) `shouldBeLiteral` empty

    it "the list version should work on a singleton list" $
      union' [simple] `shouldBeLiteral` (union simple empty)

    it "the list version should work on a list with two elements" $
      union' [simple, pcf] `shouldBeLiteral` (union simple (union pcf empty))

    it "the list version should work on a list with three elements" $
      union' [simple, pcf, infinite] `shouldBeLiteral` (union simple (union pcf (union infinite empty)))

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
      intersection simple pcf `shouldBeLiteral` (grammar "S⨯PStart" M.empty)

    it "should give an empty grammar when one of the arguments is an empty grammar" $ do
      intersection simple infinite `shouldBeLiteral` (grammar "S⨯EStart" M.empty)
      intersection infinite simple `shouldBeLiteral` (grammar "EStart⨯S" M.empty)

  describe "Inclusion" $ do
    it "should work for the worked out example" $
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

    it "reflexivity should hold on simple" $
      simple `subsetOf` simple `shouldBe` True

    it "should not hold for languages that do not intersect" $ do
      simple `subsetOf` pcf `shouldBe` False
      pcf `subsetOf` simple `shouldBe` False

    it "should hold for equal grammars" $ do
      pcf `subsetOf` pcf `shouldBe` True
      (empty::GrammarBuilder Text) `subsetOf` (empty::GrammarBuilder Text) `shouldBe` True

  describe "Equality" $ do
    it "should be true when comparing the empty grammar" $ do
      (empty::GrammarBuilder Text) == empty `shouldBe` True
      (empty::GrammarBuilder Text) `shouldBe` empty

    it "should be true when comparing the same grammar" $ do
      pcf == pcf `shouldBe` True
      pcf `shouldBe` pcf

    it "should be true when comparing the same grammar (simple)" $ do
      simple == simple `shouldBe` True
      simple `shouldBe` simple

    it "should be false when comparing different grammars" $ do
      pcf == simple `shouldBe` False
      pcf `shouldNotBe` simple

    it "should be true when comparing different grammars producing the same language" $ do
      simple == simple' `shouldBe` True
      simple `shouldBe` simple'

  describe "Integration tests" $ do
    it "union idempotence should hold for simple" $
      union simple simple `shouldBe` simple

    it "union idempotence should hold for PCF" $
      union pcf pcf `shouldBe` pcf

    it "intersection of a subset should be that subset" $
      intersection pcf pcf_sub `shouldBe` pcf_sub

    it "union absorption should hold" $
      union pcf (intersection pcf simple) `shouldBe` pcf

    it "intersection idempotence should hold for PCF" $
      intersection pcf pcf `shouldBe` pcf

    it "intersection idempotence should hold for simple" $
      intersection simple simple `shouldBe` simple

    it "intersection absorption should hold" $
      intersection pcf (union pcf simple) `shouldBe` pcf

  describe "Alphabet" $ do
    it "should correctly list the alphabet of PCF" $
      let a = M.fromList [("App", [2]), ("Abs", [3]), ("Zero", [0]), ("Succ", [1]), ("Pred", [1]), ("Ifz", [3]), ("Num", [0]), ("Fun", [2]), ("String", [0])]
      in alphabet pcf `shouldBe` a

  where
    simple = grammar "S" $ M.fromList [ ("S", [ Eps "F" ])
                                      , ("A", [ Ctor "a" [] ])
                                      , ("G", [ Ctor "g" [ "G" ]
                                              , Ctor "g" [ "A" ]])
                                      , ("F", [ Ctor "f" [ "G", "G" ]])]
    simple' = grammar "S" $ M.fromList [ ("S", [ Eps "F" ])
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
    pcf_simple = grammar "Nt0" $ M.fromList [ ("Nt5", [ Ctor "g" ["Nt5"]
                                                      , Ctor "a" []])
                                            , ("Nt4", [ Ctor "g" ["Nt5"]])
                                            , ("Nt3", [ Ctor "Zero" []
                                                      , Ctor "Succ" ["Nt3"]
                                                      , Ctor "Pred" ["Nt3"]
                                                      , Ctor "Ifz" ["Nt3", "Nt3", "Nt3"]
                                                      , Ctor "App" ["Nt3","Nt3"]
                                                      , Ctor "Abs" ["Nt1", "Nt2", "Nt3"]])
                                            , ("Nt2", [ Ctor "Num" []
                                                      , Ctor "Fun" ["Nt2","Nt2"]])
                                            , ("Nt1", [ Ctor "String" [] ])
                                            , ("Nt0", [ Ctor "f" ["Nt4", "Nt4"]
                                                      , Ctor "Zero" []
                                                      , Ctor "Succ" ["Nt3"]
                                                      , Ctor "Pred" ["Nt3"]
                                                      , Ctor "Num" []
                                                      , Ctor "Ifz" ["Nt3", "Nt3", "Nt3"]
                                                      , Ctor "Fun" ["Nt2","Nt2"]
                                                      , Ctor "App" ["Nt3","Nt3"]
                                                      , Ctor "Abs" ["Nt1", "Nt2", "Nt3"]])
                                            ]

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
