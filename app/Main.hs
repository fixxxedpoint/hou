{-# LANGUAGE FlexibleContexts #-}

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
import           Hou.HigherOrderUnification as Hou
import qualified Hou.SystemF as F
import           Hou.InferenceUtils as IU
import qualified Debug.Trace


main :: IO ()
main = do
  -- input <- getContents
  -- let term = read input
  -- print $ F.inferType term

  let term = Abs Uni (Var (0, Uni))

  let result = solvePiTerm createMapContext term
  print $ head result

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


  -- let tType = Constant ("T", starType)
  -- let fv0 = 0
  -- let pType = Abs tType starType
  -- let p = Constant ("P", pType)
  -- let term =
  --       Abs Uni
  --         (App (FreeVar (fv0, Uni)) (Var (0, Uni)) Uni)
  -- let fv0Type =
  --       buildImplication tType (Abs tType (App p (Var (0, tType)) starType))
  -- -- let expected = buildImplication tType (Abs tType (App p (Var (0, tType)) starType))
  -- let ctx = IU.add IU.createMapContext fv0 fv0Type

  -- let result = solvePiTerm ctx term

  -- Debug.Trace.traceM $ (show $ head result)

  -- let term = F.Abs "x" (Just $ F.VarType 0) $ F.Var "x" Nothing
  -- let termsType = F.Implication (F.VarType 0) (F.VarType 0)

  -- let result = head . filter ((==) (F.toTermType termsType)) $ F.toTermType <$> F.inferTypes term

  -- print $ result == F.toTermType termsType


  -- let term1 = MetaVar (0, Abs someType someType)
  -- let term2 = Abs someType $ Var (0, someType)

  -- let result = head $ preunifyAllSolutions [(term1, term2)] createListSolution
  -- print result

  -- let term1 = App (App (Constant ("->", Abs someType (Abs someType someType))) (Constant ("0", someType)) (Abs someType someType)) (Constant ("0", someType)) (someType)
  -- let term2 = MetaVar (0, someType)
  -- let equation = (term1, term2)

  -- let result = head $ preunifyAllSolutions [equation] createListSolution

  -- print $ apply result term2

  let pcpInstance = [([a], [b, a, a]), ([a, b], [a, a]), ([b, b, a], [b, b])]
  let (inferenceInstance, ctx) = createInstance createMapContext pcpInstance
  print inferenceInstance
  print $ size inferenceInstance

  let result = solvePiTerm ctx inferenceInstance

  print $ head result

size :: Term -> Integer
size (Abs _ body) = 1 + size body
size (App m n _) = 1 + size m + size n
size _ = 1

tType :: TermType
tType = Constant ("T", starType)

aConst :: Term
aConst = FreeVar (-1, Uni)

bConst :: Term
bConst = FreeVar (-2, Uni)

cConst :: Term
cConst = FreeVar (-3, tType)

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

createWord :: Main.Word -> Term
createWord []             = Abs tType (Var (0, tType))
createWord (False : rest) = Abs tType (App aConst (App (createWord rest) (Var (0, tType)) tType) Uni)
createWord (True : rest)  = Abs tType (App bConst (App (createWord rest) (Var (0, tType)) tType) Uni)

createInstance :: (Context c FreeVarName PiTermType)
               => c -> [(Main.Word, Main.Word)] -> (Term, c)
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
  -- (Abs Uni . Abs Uni . Abs Uni $
  --   App (App fConstant cConst Uni) (apply g (replicate 1 y1)) Uni, newCtx)
  -- (Abs Uni . Abs Uni . Abs Uni $ (App fConstant cConst Uni), newCtx)
  -- (App fConstant cConst Uni, newCtx)
