{-# LANGUAGE FlexibleContexts #-}

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

import qualified Debug.Trace


spec = do
  describe "infere type for a term of the form \\lambda x . x" $ do
    it "should return some type" $ do
      let term = Abs Uni (Var (0, Uni))

      let result = solvePiTerm createMapContext term
      Debug.Trace.traceM $ show $ head result

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
      let expected = fv0Type -- buildImplication tType (Abs tType (App p (Var (0, tType)) starType))
      let ctx = IU.add IU.createMapContext fv0 fv0Type

      let result = solvePiTerm ctx term

      result `shouldContain` [expected]
      Debug.Trace.traceM $ show $ head result
      -- result `shouldNotBe` []

  -- describe "force a subterm to have a dependent type" $ do
  --   it "should return a proper type" $ do
  --       let fv0 = 0
  --       let fv1 = 1
  --       let tType = Constant ("T", starType)
  --       let fv1Type = Abs tType starType
  --       let fv1Term = Constant ("P", fv1Type)
  --       let fv0Type =
  --             buildImplication
  --               (buildImplication tType (Abs tType (buildImplication (App fv1Term (Var (0, tType)) starType) (Abs (App fv1Term (Var (0, tType)) starType) (App fv1Term (Var (1, tType)) starType)))))

  --               (Abs (buildImplication tType (Abs tType (buildImplication (App fv1Term (Var (0, tType)) starType) (Abs (App fv1Term (Var (0, tType)) starType) (App fv1Term (Var (1, tType)) starType))))) tType)

  --       let term =
  --             App
  --             (FreeVar (fv0, Uni))
  --             (Abs Uni (Abs Uni (Var (0, Uni)))) Uni

  --       let ctx = IU.add IU.createMapContext fv0 fv0Type

  --       let result = solvePiTerm ctx term

  --       result `shouldContain` [tType]

  -- describe "solve an small instance of the Post Correspondence Problem" $ do
  --   it "should find some solution" $ do
  --     -- let pcpInstance = [([a], [b, a, a]), ([a, b], [a, a]), ([b, b, a], [b, b])]
  --     let pcpInstance = [([a], [a])]
  --     let (inferenceInstance, ctx) = createInstance createMapContext pcpInstance

  --     let result = solvePiTerm ctx inferenceInstance

  --     result `shouldNotBe` []

tType :: TermType
tType = Constant ("T", starType)

aConst :: Term
aConst = FreeVar (-1, Uni)

bConst :: Term
bConst = FreeVar (-2, Uni)

cConst :: Term
cConst = FreeVar (-3, Uni)

dConst :: Term
dConst = FreeVar (-4, Uni)

pConst :: Term
pConst = Constant ("P", Abs tType starType)

fConstType = Abs tType (Abs (App pConst (Var (0, tType)) starType) tType)

fConstant :: Term
fConstant = FreeVar (-5, Uni)

getFreeVarName :: Term -> FreeVarName
getFreeVarName (FreeVar (name, _)) = name

type Letter = Bool
type Word = [Letter]

a :: Letter
a = False

b :: Letter
b = True

createWord :: Hou.LambdaPiSpec.Word -> Term
createWord []             = Abs tType (Var (0, tType))
createWord (False : rest) = Abs tType (App aConst (App (createWord rest) (Var (0, tType)) tType) Uni)
createWord (True : rest)  = Abs tType (App bConst (App (createWord rest) (Var (0, tType)) tType) Uni)

createInstance :: (Context c FreeVarName PiTermType)
               => c -> [(Hou.LambdaPiSpec.Word, Hou.LambdaPiSpec.Word)] -> (Term, c)
createInstance ctx words = do
  let w1 = createWord . fst <$> words
  let w2 = createWord . snd <$> words
  let n = length words
  let apply to = foldl (\a b -> App a b Uni) to
  let f = Var (2, Uni)
  let g = Var (1, Uni)
  let h = Var (0, Uni)
  let f1 = App f (apply g (replicate n aConst)) Uni
  let h1 = App h (apply g w1) Uni
  let h2 = App h (apply g w2) Uni
  let y1 = Abs tType (Var (0, tType))
  let y2 = Abs tType dConst
  let f2 = App (App fConstant cConst Uni) (apply g (replicate n y1)) Uni
  let f3 = App (App fConstant dConst Uni) (apply g (replicate n y2)) Uni
  let tFunction = Abs tType tType
  let addToContext = foldl (\c (var, typeV) -> IU.add c (getFreeVarName var) typeV) ctx
  let newCtx = addToContext
                 [(aConst, tFunction),
                  (bConst, tFunction),
                  (cConst, tType),
                  (dConst, tType),
                  (fConstant, fConstType)]
  (Abs Uni . Abs Uni . Abs Uni $
    App (App (App (App f1 h1 Uni) h2 Uni) f2 Uni) f3 Uni,
    newCtx)
