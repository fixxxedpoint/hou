{-# LANGUAGE FlexibleContexts #-}

-- TODO: unify terms and types by introducing (Pi x:type term) [use deBruijn notation] construction.

{-|
Module      : Hou.LambdaPi
Description : Provides basic definitions and methods for type checking and type inference for a
              dependently typed lambda calculus.
Copyright   : (c) 2018 Łukasz Lachowski <l.lachowski@gmail.com>
License     : MIT, see the file LICENSE
-}
module Hou.LambdaPi where

import           Hou.HigherOrderUnification as H
import           Hou.Levels
import           Hou.InferenceUtils         as IU
import           Hou.MixedPrefix

import           Control.Monad
import           Control.Monad.Gen
import           Data.FMList                as FML
import           Data.Maybe

import           Debug.Trace


type PiTerm = Term

type PiTermType = TermType

substituteWT :: Term -> DeBruijnIndex -> Term -> Term
substituteWT new index term = case term of
  v@(Var (deBruijnIndex, varType)) -> case compare deBruijnIndex index of
    LT -> Var (deBruijnIndex, substituteWT new index varType)
    EQ -> new
    GT -> Var (deBruijnIndex-1, substituteWT new index varType)
  App a b termType -> App (substituteWT new index a) (substituteWT new index b) (substituteWT new index termType)
  Abs termType a -> Abs (substituteWT new index termType) (substituteWT (H.raise 1 new) (index+1) a)
  MetaVar (name, varType) -> MetaVar (name, substituteWT new index varType)
  Constant (name, consType) -> Constant (name, substituteWT new index consType)
  FreeVar (name, varType) -> FreeVar (name, substituteWT new index varType)
  Uni -> term

buildImplication :: Term -> Term -> Term
buildImplication t1 t2 | getTermType t1 == starType && getTermType t2 == Abs termType starType =
  App
  (App (Constant ("->", Abs starType (Abs (Abs Uni starType) starType))) t1 (Abs (Abs Uni starType) starType))
  t2 starType
buildImplication t1 t2 = Debug.Trace.traceStack "asdasd" $ error $ "term: " ++ show t1 ++ "---" ++ show t2

typeOf :: (Context c FreeVarName PiTermType)
       => c
       -> PiTerm
       -> Maybe (PiTermType, [Equation])
typeOf c t = do
  let genEnum = toEnum . (1 +) . maximum . (:) 0 . getMetaFreeVars $ t
  runGenTFrom genEnum $ do
    resultName <- gen
    let resultType = MetaVar (resultName, starType)
    eqs <- typeOf' c t resultType
    return (resultType, eqs)


typeOf' :: (Context c FreeVarName PiTermType, MonadGen MetaVariableName m, MonadPlus m)
       => c
       -> PiTerm
       -> PiTermType
       -> m [Equation]
-- TODO add typechecking for types, i.e. if types are correct
typeOf' c t tType = case t of
  FreeVar (varName, _) -> maybe mzero (\x -> return [(tType, x)]) $ IU.lookup c varName

  App t1 t2 _ -> do
    mvName <- gen
    let argType = MetaVar (mvName, starType)
    resultName <- gen
    let resultType = MetaVar (resultName, Abs termType starType)
    eq1 <- typeOf' c t1 (buildImplication argType resultType)
    eq2 <- typeOf' c t2 argType
    -- newArgName <- gen
    -- let newArg = MetaVar (newArgName, starType)
    -- return $ [(tType, App resultType newArg starType)] ++ eq1 ++ eq2
    return $ [(tType, App resultType t2 starType)] ++ eq1 ++ eq2

  Abs _ body -> do
    mvName <- gen
    let mv = MetaVar (mvName, starType)
    freeVarName <- gen
    let fvVal = (freeVarName, termType)
    let fv = FreeVar fvVal
    returnName <- gen
    let returnType = MetaVar (returnName, Abs termType starType)
    -- argName <- gen
    -- let argType = MetaVar (argName, starType)
    eqs <- typeOf' (IU.add c freeVarName mv) (substitute fv 0 body) (App returnType fv starType)
    return $ (tType, buildImplication mv returnType) : eqs
  _ -> fail "invalid term"

solvePiTerm :: (Context c FreeVarName PiTermType) => c -> PiTerm -> [PiTermType]
solvePiTerm c = FML.toList . solve' c

solve' :: (Context c FreeVarName PiTermType) => c -> PiTerm -> FML.FMList PiTermType
solve' c t = do
  (termType, equations) <- maybe mzero return $ typeOf c t
  traceM $ show termType
  traceM "---"
  traceM $ show equations
  iterDepthDefault $ do
    solution <- unifyNonDeterministic equations createListSolution
    return $ normalize $ apply solution termType
