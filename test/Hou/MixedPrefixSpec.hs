{-|
Module      : Hou.MixedPrefixSpec
Copyright   : (c) 2018 Łukasz Lachowski <l.lachowski@gmail.com>
License     : MIT, see the file LICENSE
-}
module Hou.MixedPrefixSpec where

import           Hou.HigherOrderUnification
import           Hou.MixedPrefix            as M

import           Test.Hspec


spec :: Spec
spec = do
  describe "convert to prenex normal form a term which is already in that form" $ do
    it "should return the same term" $ do
      let mv1 = (0, starType)
      let mv2 = (1, starType)
      let formula = Exists mv1 $ Exists mv2 $ Equation (MetaVar mv1) (MetaVar mv2)

      let result = toPrenexNormalForm formula

      result `shouldBe` (PNF { M.head = [QExists mv1, QExists mv2], body = [(MetaVar mv1, MetaVar mv2)] })

  describe "convert to prenex normal form a term with two different quantifiers at different levels" $ do
    it "should return prenex version of that term" $ do
      let mv1 = (0, starType)
      let mv2 = (1, starType)
      let mv3 = (1, starType)
      let formula = Exists mv1 $ Exists mv2 $ And (Equation (MetaVar mv1) (MetaVar mv2)) (ForAll mv3 (Equation (MetaVar mv2) (MetaVar mv3)))

      let result = toPrenexNormalForm formula

      result `shouldBe` (PNF { M.head = [QExists mv1, QExists mv2, QForAll mv3], body = [(MetaVar mv1, MetaVar mv2), (MetaVar mv2, MetaVar mv3)] })

  describe "converting to prenex normal form a term with one 'and' branch" $ do
    it "should return prenex normal form where quantifiers are in first-left order" $ do
      let mv1 = (0, starType)
      let mv2 = (1, starType)
      let mv3 = (1, starType)
      let formula = Exists mv1 $ And (Exists mv2 $ Equation (MetaVar mv1) (MetaVar mv2)) (ForAll mv3 (Equation (MetaVar mv2) (MetaVar mv3)))

      let result = toPrenexNormalForm formula

      result `shouldBe` (PNF { M.head = [QExists mv1, QExists mv2, QForAll mv3], body = [(MetaVar mv1, MetaVar mv2), (MetaVar mv2, MetaVar mv3)] })

  describe "converting to raised prenex normal form a term that is already in that form" $ do
    it "should return a term in the same form" $ do
      let mv1 = (0, starType)
      let mv2 = (1, starType)
      let formula = (PNF { M.head = [QExists mv1, QExists mv2], body = [(MetaVar mv1, MetaVar mv2)] })

      let (result, _) = raise formula createListSolution

      result `shouldBe` (RNF { exists = [mv1, mv2], forall = [], eqs = [(MetaVar mv1, MetaVar mv2)] })

  describe "converting to raised prenex normal form a term that requires only one raising" $ do
    it "should properly raise such formula and create proper substitution" $ do
      let mv1 = (0, starType)
      let mv2 = (1, starType)
      let formula = (PNF { M.head = [QForAll mv1, QExists mv2], body = [(MetaVar mv1, MetaVar mv2)] })

      let (result, s) = raise formula createListSolution

      forall result `shouldBe` [mv1]

      let mv2' = apply s (MetaVar mv2)
      let mv2'Head = (\((MetaVar mv), _) -> mv) $ getHead mv2'

      result `shouldBe` (RNF { exists = [mv2'Head], forall = [mv1], eqs = [(MetaVar mv1, mv2')] })
      mv2' `shouldBe` App (MetaVar mv2'Head) (MetaVar mv1) starType

  describe "converting to raised prenex normal form a term that has two quantifiers for raising, one after another" $ do
    it "should properly raise such formula and create proper substitution" $ do
      let mv1 = (0, starType)
      let mv2 = (1, starType)
      let mv3 = (2, starType)
      let formula = (PNF {
                        M.head = [QForAll mv1, QExists mv2, QExists mv3],
                        body = [(MetaVar mv1, MetaVar mv2), (MetaVar mv2, MetaVar mv3)]
                        })

      let (result, s) = raise formula createListSolution

      let mv2' = apply s (MetaVar mv2)
      let mv2'Head = (\((MetaVar mv), _) -> mv) $ getHead mv2'
      let mv3' = apply s (MetaVar mv3)
      let mv3'Head = (\((MetaVar mv), _) -> mv) $ getHead mv3'

      result `shouldBe` (RNF { exists = [mv2'Head, mv3'Head], forall = [mv1], eqs = [(MetaVar mv1, mv2'), (mv2', mv3')] })
      mv2' `shouldBe` App (MetaVar mv2'Head) (MetaVar mv1) starType
      mv3' `shouldBe` App (MetaVar mv3'Head) (MetaVar mv1) starType

  describe "converting to raised prenex normal form a term that has two quantifiers for raising, \
           \seperated by one general quantifier" $ do
    it "should properly raise such formula and create proper substitution" $ do
      let mv1 = (0, starType)
      let mv2 = (1, starType)
      let mv3 = (2, starType)
      let mv4 = (3, starType)
      let formula = (PNF {
                        M.head = [QForAll mv1, QExists mv2, QForAll mv3, QExists mv4],
                        body = [(MetaVar mv1, MetaVar mv2), (MetaVar mv2, MetaVar mv3), (MetaVar mv3, MetaVar mv4)]
                        })

      let (result, s) = raise formula createListSolution

      let mv2' = apply s (MetaVar mv2)
      let mv2'Head = (\((MetaVar mv), _) -> mv) $ getHead mv2'
      let mv4' = apply s (MetaVar mv4)
      let mv4'Head = (\((MetaVar mv), _) -> mv) $ getHead mv4'

      result `shouldBe` (RNF {
                            exists = [mv2'Head, mv4'Head],
                            forall = [mv1, mv3], eqs = [(MetaVar mv1, mv2'), (mv2', MetaVar mv3), (MetaVar mv3, mv4')]
                            })
      mv2' `shouldBe` App (MetaVar mv2'Head) (MetaVar mv1) starType
      mv4' `shouldBe` App (App (MetaVar mv4'Head) (MetaVar mv1) (Pi starType starType)) (MetaVar mv3) starType

  describe "toEquation on single equation" $ do
    it "should return a correct equation" $ do
      let mv1 = (1, starType)
      let mv2 = (2, starType)
      let formula = RNF { exists = [mv1, mv2], forall = [], eqs = [(MetaVar mv1, MetaVar mv2)] }

      let result1 =
            App
              (App
                 (Abs (varType 0) (Abs (varType 0) (Abs (Pi (varType 0) (varType 1))
                   (App
                     (Var (0,Pi (varType 0) (varType 1)))
                     (Var (2,varType 0))
                     (varType 1)))))
                 (MetaVar mv1)
                 (Pi (varType 0) (Pi (Pi (varType 0) (varType 1)) (varType 1)))
              )
              (MetaVar mv2)
              (Pi (Pi (varType 0) (varType 1)) (varType 1))

      let result2 =
            App
              (App
                 (Abs (varType 0) (Abs (varType 0) (Abs (Pi (varType 0) (varType 1))
                   (App
                     (Var (0,Pi (varType 0) (varType 1)))
                     (Var (1,varType 0))
                     (varType 1)))))
                 (MetaVar mv1)
                 (Pi (varType 0) (Pi (Pi (varType 0) (varType 1)) (varType 1)))
              )
              (MetaVar mv2)
              (Pi (Pi (varType 0) (varType 1)) (varType 1))

      toEquation formula `shouldBe` (result1, result2)
