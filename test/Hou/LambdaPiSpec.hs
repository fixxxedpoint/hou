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


spec = do
  describe "infere type for a term of the form \\lambda x . x" $ do
    it "should return some type" $ do
      let term = Abs Uni (Var (0, Uni))

      let result = solvePiTerm createMapContext term
      traceM $ show $ head result

      result `shouldNotBe` []

  describe "infere type for a term of the form \\lambda x . Fx, where F is of type \\lambda x . Px and P is \\lambda T . *" $ do
    it "should return some type" $ do
      let tType = Constant ("T", starType)
      let fv0 = 0
      let pType = Abs tType starType
      let p = Constant ("P", pType)
      let term =
            Abs Uni
              (App (FreeVar (fv0, Uni)) (Var (0, Uni)) Uni)
      let fv0Type =
            buildImplication tType (Abs tType (App p (Var (0, tType)) starType))
      let expected = buildImplication tType (Abs tType (App p (Var (0, tType)) starType))
      let ctx = IU.add IU.createMapContext fv0 fv0Type

      let result = solvePiTerm ctx term

      traceM $ (show $ head result)

      result `shouldNotBe` []

  describe "force a subterm to have a dependent type" $ do
    it "should return a proper type" $ do
      let fv0 = 0
      let fv1 = 1
      let tType = Constant ("T", starType)
      let fv1Type = Abs tType starType
      let fv1Term = Constant ("P", fv1Type)
      -- FIXME: this type looks wrong
      let fv0Type =
            buildImplication
              (buildImplication tType (Abs tType (buildImplication (App fv1Term (Var (0, tType)) starType) (Abs (App fv1Term (Var (0, tType)) starType) (App fv1Term (Var (1, tType)) starType)))))

              (Abs (buildImplication tType (Abs tType (buildImplication (App fv1Term (Var (0, tType)) starType) (Abs (App fv1Term (Var (0, tType)) starType) (App fv1Term (Var (1, tType)) starType))))) tType)

      Debug.Trace.traceM $ "fv0Type: " ++ show fv0Type
      let term =
            App
            (FreeVar (fv0, fv0Type))
            (Abs Uni (Abs Uni (Var (0, Uni)))) Uni

      let ctx = IU.add IU.createMapContext fv0 fv0Type

      let result = solvePiTerm ctx term

      traceM $ show $ head result

      result `shouldNotBe` []

  -- describe "solve an small instance of the Post Correspondence Problem" $ do
  --   it "should find some solution" $ do
  --     let a = 1
  --     let b = 2
  --     let c = 3
  --     let d = 4
  --     let p = 5
  --     let fVar = 6

  --     let tType = Constant ("T", starType)
  --     let aType = Abs (Constant ("T", starType)) (Constant ("T", starType))
  --     let bType = aType
  --     let cType = Constant ("T", starType)
  --     let dType = cType
  --     let pType = Abs (Constant ("T", starType)) starType
  --     let fType = Abs tType $ Abs (App (FreeVar (p, Uni)) (Var (0, tType)) Uni) tType

  --     let phi1 = Abs tType (App (FreeVar (a, aType)) (App (Abs tType (Var (0, tType))) (Var (0, tType)) tType) tType)
  --     let phi2 = Abs tType (App (FreeVar (a, aType)) (App (Abs tType (Var (0, tType))) (Var (0, tType)) tType) tType)
  --     let phi3 = Abs tType (App (FreeVar (a, aType)) (App (Abs tType (Var (0, tType))) (Var (0, tType)) tType) tType)
  --     let v1 = Abs tType (App (FreeVar (a, aType)) (App (Abs tType (Var (0, tType))) (Var (0, tType)) tType) tType)
  --     let v2 = Abs tType (App (FreeVar (a, aType)) (App (Abs tType (Var (0, tType))) (Var (0, tType)) tType) tType)
  --     let v3 = Abs tType (App (FreeVar (a, aType)) (App (Abs tType (Var (0, tType))) (Var (0, tType)) tType) tType)

  --     let f = App (Var (2, Uni))
  --                 (App (App (App (Var (1, Uni))
  --                                (FreeVar (a, Uni)) Uni)
  --                           (FreeVar (a, Uni)) Uni)
  --                      (FreeVar (a, Uni)) Uni)
  --                 Uni

  --     let h1 = App (Var (0, Uni))
  --                 (App (App (App (Var (1, Uni))
  --                                phi1 Uni)
  --                           phi2 Uni)
  --                      phi3 Uni)
  --                 Uni
  --     let h2 = App (Var (0, Uni))
  --                 (App (App (App (Var (1, Uni))
  --                                v1 Uni)
  --                           v2 Uni)
  --                      v3 Uni)
  --                 Uni
  --     let g1 = App (App (App (Var (1, Uni)) (Abs Uni (Var (0, Uni))) Uni) (Abs Uni (Var (0, Uni))) Uni) (Abs Uni (Var (0, Uni))) Uni

  --     let g2 = App (App (App (Var (1, Uni)) (Abs Uni (FreeVar (d, Uni))) Uni) (Abs Uni (FreeVar (d, Uni))) Uni) (Abs Uni (FreeVar (d, Uni))) Uni

  --     let f1 = App (App (FreeVar (fVar, Uni)) (FreeVar (c, Uni)) Uni) g1 Uni
  --     let f2 = App (App (FreeVar (fVar, Uni)) (FreeVar (d, Uni)) Uni) g2 Uni

  --     let term =
  --           Abs Uni $ Abs Uni $ Abs Uni $ App (App (App (App f h1 Uni) h2 Uni) f1 Uni) f2 Uni

  --     let ctx = (((((IU.createMapContext `IU.add` a $ aType) `IU.add` b $ bType) `IU.add` c $ cType) `IU.add` d $ dType) `IU.add` p $ pType) `IU.add` fVar $ fType

  --     let result = solvePiTerm ctx term

  --     result `shouldNotBe` []

  -- describe "solve an easy instance of the Post Correspondence Problem by means of type inference" $ do
  --   it "should return a proper type that encodes a solution for the Post Corresponce Problem" $ do
  --     -- TODO: create a parser for lambda terms
  --     -- let term = L f . L g . L h . (f (g a a a))
  --     --                              (h (g p1 p2 p3))
  --     --                              (h (g q1 q2 q3))
  --     --                              (F c (g (L y . y) (L y . y) (L y . y)))
  --     --                              (F d (g (L y . d) (L y . d) (L y . d)))
  --     let tType = Constant ("T", starType)
  --     let fVar = 7
  --     let c = 8
  --     let d = 9
  --     let a = 10
  --     let b = 20
  --     let p = 11

  --     let aType = Abs (Constant ("T", starType)) (Constant ("T", starType))
  --     let bType = aType
  --     let cType = Constant ("T", starType)
  --     let dType = cType
  --     let pType = Abs (Constant ("T", starType)) starType
  --     let fType = Abs tType $ Abs (App (FreeVar (p, Uni)) (Var (0, tType)) Uni) tType

  --     let phi1 = Abs tType (App (FreeVar (a, aType)) (App (Abs tType (Var (0, tType))) (Var (0, tType)) tType) tType)
  --     let phi2 = Abs tType (App (FreeVar (a, aType)) (App (FreeVar (b, bType)) (App (Abs tType (Var (0, tType))) (Var (0, tType)) tType) tType ) tType)
  --     let phi3 = Abs tType (App (FreeVar (b, bType)) (App (FreeVar (b, bType)) (App (FreeVar (a, aType)) (App (Abs tType (Var (0, tType))) (Var (0, tType)) tType) tType ) tType ) tType)
  --     let v1 = Abs tType (App (FreeVar (b, bType)) (App (FreeVar (a, aType)) (App (FreeVar (a, aType)) (App (Abs tType (Var (0, tType))) (Var (0, tType)) tType) tType ) tType ) tType)
  --     let v2 = Abs tType (App (FreeVar (a, aType)) (App (FreeVar (a, aType)) (App (Abs tType (Var (0, tType))) (Var (0, tType)) tType) tType ) tType)
  --     let v3 = Abs tType (App (FreeVar (b, bType)) (App (FreeVar (b, bType)) (App (Abs tType (Var (0, tType))) (Var (0, tType)) tType) tType ) tType)

  --     let f = App (Var (2, Uni))
  --                 (App (App (App (Var (1, Uni))
  --                                (FreeVar (a, Uni)) Uni)
  --                           (FreeVar (a, Uni)) Uni)
  --                      (FreeVar (a, Uni)) Uni)
  --                 Uni

  --     let h1 = App (Var (0, Uni))
  --                 (App (App (App (Var (1, Uni))
  --                                phi1 Uni)
  --                           phi2 Uni)
  --                      phi3 Uni)
  --                 Uni
  --     let h2 = App (Var (0, Uni))
  --                 (App (App (App (Var (1, Uni))
  --                                v1 Uni)
  --                           v2 Uni)
  --                      v3 Uni)
  --                 Uni
  --     let g1 = App (App (App (Var (1, Uni)) (Abs Uni (Var (0, Uni))) Uni) (Abs Uni (Var (0, Uni))) Uni) (Abs Uni (Var (0, Uni))) Uni

  --     let g2 = App (App (App (Var (1, Uni)) (Abs Uni (FreeVar (d, Uni))) Uni) (Abs Uni (FreeVar (d, Uni))) Uni) (Abs Uni (FreeVar (d, Uni))) Uni

  --     let f1 = App (App (FreeVar (fVar, Uni)) (FreeVar (c, Uni)) Uni) g1 Uni
  --     let f2 = App (App (FreeVar (fVar, Uni)) (FreeVar (c, Uni)) Uni) g2 Uni

  --     let term =
  --           Abs Uni $ Abs Uni $ Abs Uni $ App (App (App (App f h1 Uni) h2 Uni) f1 Uni) f2 Uni

  --     let ctx = (((((IU.createMapContext `IU.add` a $ aType) `IU.add` b $ bType) `IU.add` c $ cType) `IU.add` d $ dType) `IU.add` p $ pType) `IU.add` fVar $ fType

  --     let result = solvePiTerm ctx term

  --     result `shouldNotBe` []
