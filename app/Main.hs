{-|
Module      : Main
Description : Simple main module trying to parse a lambda term from the standard input and returning
              its type.
Copyright   : (c) 2018 Łukasz Lachowski <l.lachowski@gmail.com>
License     : MIT, see the file LICENSE
-}
module Main where

-- import           Hou.SystemF
import           Hou.LambdaPi
import           Hou.HigherOrderUnification
import qualified Hou.SystemF as F
import           Hou.InferenceUtils as IU
import           Debug.Trace


main :: IO ()
main = do
  -- input <- getContents
  -- let term = read input
  -- print $ F.inferType term

  -- let term = Abs Uni (Var (0, Uni))

  -- let result = solvePiTerm createMapContext term
  -- print $ head result

  -- let fv0 = 0
  -- let fv1 = 1
  -- let tType = Constant ("T", starType)
  -- let fv1Type = Abs tType starType
  -- let fv1Term = Constant ("P", fv1Type)
  -- let fv0Type =
  --       buildImplication
  --         (buildImplication tType (Abs tType (buildImplication (App fv1Term (Var (0, tType)) starType) (Abs (App fv1Term (Var (0, tType)) starType) (App fv1Term (Var (1, tType)) starType)))))

  --         (Abs (buildImplication tType (Abs tType (buildImplication (App fv1Term (Var (0, tType)) starType) (Abs (App fv1Term (Var (0, tType)) starType) (App fv1Term (Var (1, tType)) starType))))) tType)

  -- -- Debug.Trace.traceM $ "fv0's type: " ++ show fv0Type

  -- let term =
  --       App
  --       (FreeVar (fv0, Uni))
  --       (Abs Uni (Abs Uni (Var (0, Uni)))) Uni

  -- let ctx = IU.add IU.createMapContext fv0 fv0Type

  -- let result = solvePiTerm ctx term

  -- putStrLn $ "result type: " ++ show (head result)


  let tType = Constant ("T", starType)
  let fv0 = 0
  let pType = Abs tType starType
  let p = Constant ("P", pType)
  let term =
        Abs Uni
          (App (FreeVar (fv0, Uni)) (Var (0, Uni)) Uni)
  let fv0Type =
        buildImplication tType (Abs tType (App p (Var (0, tType)) starType))
  -- let expected = buildImplication tType (Abs tType (App p (Var (0, tType)) starType))
  let ctx = IU.add IU.createMapContext fv0 fv0Type

  let result = solvePiTerm ctx term

  traceM $ (show $ head result)

  -- let term = F.Abs "x" (Just $ F.VarType 0) $ F.Var "x" Nothing
  -- let termsType = F.Implication (F.VarType 0) (F.VarType 0)

  -- let result = head . filter ((==) (F.toTermType termsType)) $ F.toTermType <$> F.inferTypes term

  -- print $ result == F.toTermType termsType

