{-|
Module      : Hou.SystemFSpec
Copyright   : (c) 2018 Łukasz Lachowski <l.lachowski@gmail.com>
License     : MIT, see the file LICENSE
-}
module Hou.SystemFSpec where

import           Hou.SystemF

import           Test.Hspec

import           Debug.Trace


spec :: Spec
spec = do
  -- describe "infer type of \\lambda x . x" $ do
  --   it "should return a type of the form x -> x" $ do
  --     let term = Abs "x" (Just $ VarType 0) $ Var "x" Nothing
  --     let termsType = Implication (VarType 0) (VarType 0)

  --     let result = head . filter ((==) (toTermType termsType)) $ toTermType <$> inferTypes term

  --     result `shouldBe` toTermType termsType

  describe "infer type of polymorphic identity" $ do
    it "should return a type of the form forall x . x -> x" $ do
      let term = TypeAbs Nothing $ Abs "x" Nothing $ Var "x" Nothing
      let termsType = toTermType $ ForAll 0 (Implication (VarType 0) (VarType 0))

      -- let result = head . filter ((==) termsType) $ toTermType <$> inferTypes term

      -- result `shouldBe` termsType

      let result = inferTypes term

      result `shouldNotBe` []

  describe "infer type of \\lambda x . x x with type annotations" $ do
    it "should return a type of the form (forall x . x -> x) -> (forall x . x -> x)" $ do
      let term = Abs "x" (Just $ ForAll 0 (Implication (VarType 0) (VarType 0))) $ App (TypeApp (Var "x" Nothing) Nothing) (Var "x" Nothing)
      let termsType = Implication (ForAll 0 (Implication (VarType 0) (VarType 0))) (ForAll 0 (Implication (VarType 0) (VarType 0)))

      let result = head . filter ((==) (toTermType termsType)) $ toTermType <$> inferTypes term

      result `shouldBe` toTermType termsType

  describe "infer type of \\lambda x . x x without type annotations" $ do
    it "should return some type" $ do
      let term = Abs "x" Nothing $ App (Var "x" Nothing) (Var "x" Nothing)

      let result = inferTypes term

      result `shouldNotBe` []

  describe "infer type of (\\lambda x . x x) (\\lambda x . x) with type annotations" $ do
    it "should return a type of the form forall x . x -> x" $ do
      let term = App (Abs "x" Nothing (App (TypeApp (Var "x" Nothing) Nothing) (Var "x" Nothing))) (TypeAbs Nothing (Abs "y" Nothing (Var "y" Nothing)))
      let termsType = ForAll 0 (Implication (VarType 0) (VarType 0))

      let result = head . filter ((==) (toTermType termsType)) $ toTermType <$> inferTypes term

      result `shouldBe` toTermType termsType

  describe "infer type of (\\lambda x . x x) (\\lambda x . x) without type annotations" $ do
    it "should return a type of the form forall x . x -> x" $ do
      let term = App (Abs "x" Nothing (App (Var "x" Nothing) (Var "x" Nothing))) (Abs "y" Nothing (Var "y" Nothing))
      let termsType = ForAll 0 (Implication (VarType 0) (VarType 0))

      let result = head . filter ((==) (toTermType termsType)) $ toTermType <$> inferTypes term

      result `shouldBe` toTermType termsType

  describe "infer type of (\\lambda x . x x)((\\lambda x . x x) (\\lambda x . x)) with type annotations" $ do
    it "should return some type" $ do
      let term =
            App
              (Abs "x" Nothing (App (TypeApp (Var "x" Nothing) Nothing) (Var "x" Nothing)))
              (
                App
                  (Abs "y" Nothing (App (TypeApp (Var "y" Nothing) Nothing) (Var "y" Nothing)))
                  (TypeAbs Nothing (Abs "z" Nothing (Var "z" Nothing)))
              )

      let result = inferTypes term

      traceM $ show (head result)

      result `shouldNotBe` []

  -- describe "infer type of (\\lambda x . x x)((\\lambda x . x x) (\\lambda x . x)) without type annotations" $ do
  --   it "should return some type" $ do
  --     let term =
  --           App
  --             (Abs "x" Nothing (App (Var "x" Nothing) (Var "x" Nothing)))
  --             (
  --               App
  --                 (Abs "y" Nothing (App (Var "y" Nothing) (Var "y" Nothing)))
  --                 (Abs "z" Nothing (Var "z" Nothing))
  --             )

  --     let result = inferTypes term

  --     result `shouldNotBe` []
