{-|
Module      : Hou.HigherOrderUnificationSpec
Copyright   : (c) 2018 Łukasz Lachowski <l.lachowski@gmail.com>
License     : MIT, see the file LICENSE
-}
module Hou.HigherOrderUnificationSpec where

import           Hou.HigherOrderUnification

import           Test.Hspec
import qualified Data.FMList as FML


spec :: Spec
spec = do
  Hou.HigherOrderUnificationSpec.normalize
  preunify

normalize :: Spec
normalize = do
  describe "normalize (\\lambda x . x) (\\lambda x . x)" $ do
    it "should return \\lambda x . x" $ do
      let term = App (Abs (Abs (Abs someType someType) (Abs someType someType)) (Var (0, (Abs someType someType)))) (Abs someType (Var (0, someType))) (Abs someType someType)

      let result = FML.head $ Hou.HigherOrderUnification.normalize term

      result `shouldBe` Abs someType (Var (0, someType))

  describe "normalize (\\lambda x . \\lambda y . x) z" $ do
    it "should return \\lambda y . z" $ do
      let term = App (Abs someType (Abs someType (Var (1, someType)))) (Var (2, someType)) (Abs someType someType)

      let result = FML.head $ Hou.HigherOrderUnification.normalize term

      result `shouldBe` Abs someType (Var (3, someType))

preunify :: Spec
preunify = do
  describe "preunify already solved" $ do
    it "does not change equation if it is already equal" $ do
      let term = Abs someType $ Var (0, someType)
      let equation = (term, term)

      let result = head $ preunifyAllSolutions [equation] createListSolution

      apply result term `shouldBe` term

  describe "preunify easy" $ do
    it "should create a substition for flex-rigid term" $ do
      let term1 = MetaVar (0, Abs someType someType)
      let term2 = Abs someType $ Var (0, someType)

      let result = head $ preunifyAllSolutions [(term1, term2)] createListSolution

      apply result term1 `shouldBe` term2

  describe "preunify equation requiring single beta reduction" $ do
    it "checks terms modulo beta equality" $ do
      let term1 = App (Abs someType (Var (0, someType))) (MetaVar (1, someType)) (someType)
      let term2 = MetaVar (0, someType)
      let equation = (term1, term2)

      let result = head $ preunifyAllSolutions [equation] createListSolution

      apply result term2 `shouldBe` term2

  describe "preunify simple implication" $ do
    it "should return proper substitution" $ do
      let term1 = App (App (Constant ("->", Abs someType (Abs someType someType))) (FreeVar (0, someType)) (Abs someType someType)) (FreeVar (0, someType)) (someType)
      let term2 = MetaVar (0, someType)
      let equation = (term1, term2)

      let result = head $ preunifyAllSolutions [equation] createListSolution

      apply result term2 `shouldBe` term1
