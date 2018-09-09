{-# OPTIONS_GHC -F -pgmF hspec-discover #-}

{-|
Module      : Main
Copyright   : (c) 2018 Łukasz Lachowski <l.lachowski@gmail.com>
License     : MIT, see the file LICENSE
-}
module Main where

import           Test.Hspec

import qualified Hou.HigherOrderUnificationSpec
import qualified Hou.LambdaPiSpec
import qualified Hou.LevelsSpec
import qualified Hou.MixedPrefixSpec
import qualified Hou.SystemFSpec


main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "HigherOrderUnification" Hou.HigherOrderUnificationSpec.spec
  -- describe "LambdaPi" Hou.LambdaPiSpec.spec
  describe "Levels" Hou.LevelsSpec.spec
  describe "MixedPrefix" Hou.MixedPrefixSpec.spec
  describe "SystemF" Hou.SystemFSpec.spec
