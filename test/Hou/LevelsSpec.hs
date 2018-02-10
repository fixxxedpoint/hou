{-|
Module      : Hou.LevelsSpec
Copyright   : (c) 2018 Łukasz Lachowski <l.lachowski@gmail.com>
License     : MIT, see the file LICENSE
-}
module Hou.LevelsSpec where

import           Hou.Levels    as L

import           Control.Monad
import           Data.FMList   as FML
import           Test.Hspec


spec :: Spec
spec = do
  describe "search for a Pythagorean triple" $ do
    it "should return some Pythagorean triple" $ do

      let pyTriples = do {
          a <- anyOf [1,2..];
          b <- anyOf [a+1, a+2..];
          c <- anyOf [b+1, b+2..];
          guard (a*a + b*b == c*c);
          return (a, b, c);
      }

      let (a, b, c) = FML.head . iterDepth 1 $ pyTriples

      (a*a + b*b) `shouldBe` (c*c)
