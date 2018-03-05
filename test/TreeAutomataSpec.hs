{-# LANGUAGE OverloadedStrings #-}
module TreeAutomataSpec(main, spec) where

import           Control.Monad

import qualified Data.Map as M

import           TreeAutomata

import           Test.Hspec
import           Test.HUnit

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

  describe "Productivity" $ do
    it "should give all nonterminals for PCF" $
      map (`isProductive` pcf) ["Exp", "Type", "String", "PStart"] `shouldBe` [True, True, True, True]

    it "should give no nonterminals for infinite" $
      map (`isProductive` infinite) ["foo", "EStart"] `shouldBe` [False, False]

    it "should give all nonterminals for simple" $
      map (`isProductive` simple) ["S", "A", "G", "F"] `shouldBe` [True, True, True, True]

    it "should give all nonterminals for simple'" $
      map (`isProductive` simple') ["S", "A", "G", "H", "F"] `shouldBe` [True, True, True, True, True]

    it "should give all nonterminals for the PCF subset" $
      map (`isProductive` pcf_sub) ["PSStart", "Exp", "Type"] `shouldBe` [True, True, True]

    it "should give all nonterminals for the union of PCF and simple" $
      map (`isProductive` pcf_simple) ["Start0", "PStart", "S", "A", "G", "F", "Exp", "Type", "Type"] `shouldBe` [True, True, True, True, True, True, True, True, True]

  describe "Emptiness" $ do
    it "should be true on the empty grammar" $
      isEmpty (TreeAutomata.empty "Start") `shouldBe` True

    it "should be true on the infinite infinite grammar" $
      isEmpty infinite `shouldBe` True

    it "should be false on the simple grammar" $
      isEmpty simple `shouldBe` False

    it "should be false on the PCF grammar" $
      isEmpty pcf `shouldBe` False

    it "should be false on the subset of PCF" $
      isEmpty pcf_sub `shouldBe` False

  describe "Union" $ do
    it "should work on the union of two small grammars" $
      let g1 = Grammar "Start1" $ M.fromList [ ("Start1", [ Eps "Exp" ])
                                             , ("Exp", [ Ctor "Zero" [] ])]
          g2 = Grammar "Start2" $ M.fromList [ ("Start2", [ Eps "Type" ])
                                             , ("Type", [ Ctor "Num" [] ])]
          g3 = Grammar "Start0" $ M.fromList [ ("Start0", [ Eps "Start1", Eps "Start2" ])
                                             , ("Start1", [ Eps "Exp" ])
                                             , ("Start2", [ Eps "Type" ])
                                             , ("Exp", [ Ctor "Zero" [] ])
                                             , ("Type", [ Ctor "Num" [] ])]
      in union g1 g2 `shouldBeLiteral` g3

    it "should work on the union of the simple and PCF grammars" $
      union pcf simple `shouldBeLiteral` pcf_simple

  describe "Intersection" $ do
    it "of a subset of the PCF grammar should be that subset" $
      intersection pcf pcf_sub `shouldBeLiteral` (Grammar "PStart⨯PSStart" $
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
      intersection simple pcf `shouldBeLiteral` (Grammar "S⨯PStart" M.empty)

    it "should give an empty grammar when one of the arguments is an empty grammar" $ do
      intersection simple infinite `shouldBeLiteral` (Grammar "S⨯EStart" M.empty)
      intersection infinite simple `shouldBeLiteral` (Grammar "EStart⨯S" M.empty)

  describe "Inclusion" $ do
    it "should work for the worked out example" $
      let g = Grammar "S" $ M.fromList [("S", [ Ctor "f" ["A"]
                                              , Ctor "c" []
                                              , Ctor "f" ["B"]])
                                       ,("A", [ Ctor "g" ["S"]
                                              , Ctor "e" []])
                                       ,("B", [ Ctor "b" []])]
          g' = Grammar "S'" $ M.fromList [("S'", [ Ctor "f" ["A'"]
                                                 , Ctor "c" []
                                                 , Ctor "f" ["B'"]])
                                         ,("A'", [ Ctor "g" ["S'"]
                                                 , Ctor "e" []])
                                         ,("B'", [ Ctor "b" []])]
      in g `subsetOf` g' `shouldBe` True

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

  describe "Equality" $ do
    it "should be true when comparing the same grammar" $ do
      pcf == pcf `shouldBe` True
      pcf `shouldBe` pcf

    it "should be false when comparing different grammars" $ do
      pcf == simple `shouldBe` False
      pcf `shouldNotBe` simple

    it "should be true when comparing different grammars producing the same language" $ do
      simple == simple' `shouldBe` True
      simple `shouldBe` simple'

  where
    simple = Grammar "S" $ M.fromList [ ("S", [ Eps "F" ])
                                      , ("A", [ Ctor "a" [] ])
                                      , ("G", [ Ctor "g" [ "G" ]
                                              , Ctor "g" [ "A" ]])
                                      , ("F", [ Ctor "f" [ "G", "G" ]])]
    simple' = Grammar "S" $ M.fromList [ ("S", [ Eps "F" ])
                                       , ("A", [ Ctor "a" [] ])
                                       , ("G", [ Ctor "g" [ "G" ]
                                               , Ctor "g" [ "A" ]])
                                       , ("H", [ Eps "G" ])
                                       , ("F", [ Ctor "f" [ "G", "H" ]])]
    infinite = Grammar "EStart" $ M.fromList [ ("EStart", [ Eps "foo" ])
                                             , ("foo", [ Ctor "Bar" ["foo"]])]
    pcf = Grammar "PStart" $ M.fromList [ ("PStart", [ Eps "Exp"
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
    pcf_sub = Grammar "PSStart" $ M.fromList [ ("PSStart", [ Eps "Exp"
                                                           , Eps "Type" ])
                                             , ("Exp", [ Ctor "Succ" [ "Exp" ]
                                                       , Ctor "Pred" [ "Exp" ]
                                                       , Ctor "Zero" []])
                                             , ("Type", [ Ctor "Num" []
                                                        , Ctor "Fun" ["Type", "Type"]])]
    pcf_simple = Grammar "Start0" $ M.fromList [ ("Start0", [ Eps "PStart"
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
    shouldBeLiteral :: Grammar -> Grammar -> Expectation
    actual `shouldBeLiteral` expected = let
      (Grammar start1 prods1) = actual
      (Grammar start2 prods2) = expected
      in
      -- TODO: apparently the order of the right hand sides in the maps matters. For now, just make the right order in the test cases,
      -- but eventually we should implement a custom equality check that does not depend on order.
        unless (start1 == start2 && prods1 == prods2)
          (assertFailure $ "Grammars are not literally equal.\nExpected:\n\n" ++ show expected ++ "\nbut got:\n\n" ++ show actual)
