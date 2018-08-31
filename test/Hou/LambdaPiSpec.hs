{-|
Module      : Hou.Hou.LambdaPiSpec
Copyright   : (c) 2018 Łukasz Lachowski <l.lachowski@gmail.com>
License     : MIT, see the file LICENSE
-}
module Hou.LambdaPiSpec where

import           Hou.HigherOrderUnification
import           Hou.InferenceUtils as IU
import           Hou.LambdaPi

import           Test.Hspec
import qualified Data.FMList as FML
import           Debug.Trace


spec :: Spec
spec = do
  describe "infere type for a term of the form \\lambda x. x" $ do
    it "should return some type" $ do
      let term = Abs Uni (Var (0, Uni))

      let result = solvePiTerm createMapContext term
      traceM $ show $ head result

      solvePiTerm createMapContext term `shouldNotBe` []

  describe "infere type for a term of the form \\lambda x. Px, where P is of type A -> *" $ do
    it "should return some type" $ do
      let term =
            Abs Uni
              (App (FreeVar (0, Uni)) (Var (0, Uni)) Uni)
      let fv0Type =
            (Pi (Constant ("T", Uni))
              (Pi
                (App (FreeVar (1, Uni)) (Var (0, Constant ("T", Uni))) Uni)
                (Constant ("T", Uni))))
      let fv1Type = (Pi (Constant ("T", Uni)) Uni)
      let ctx = IU.add (IU.add IU.createMapContext 0 fv0Type) 1 fv1Type
      let expected = Pi (Constant ("T",Uni)) (Pi (App (FreeVar (1,Uni)) (Var (0,Constant ("T",Uni))) Uni) (Constant ("T",Uni)))

      let result = solvePiTerm ctx term

      traceM $ show $ head result

      result `shouldNotBe` []
      filter ((==) expected) result `shouldNotBe` []
