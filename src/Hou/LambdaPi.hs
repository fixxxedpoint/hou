-- TODO: Consider some approach simillar to pfenning and add a new constant PI : (M -> *) -> * (M is
-- a metavariable) and use it for example when you encounter an abstraction.

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}

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
import           Hou.InferenceUtils         as IU
import           Hou.Levels
import           Hou.MixedPrefix
import           Hou.Trace

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Gen
import           Data.FMList                as FML
import           Data.Maybe


type PiTerm = Term

type PiTermType = TermType

runTranslate :: (Context c FreeVarName PiTermType) => c -> PiTerm -> ([Equation], PiTermType) -- (HouFormula, PiTermType)
runTranslate c t =
  let genEnum = toEnum . (1 +) . maximum . (:) 0 . getMetaFreeVars $ t in
  runGenFrom genEnum $ do
    resultName <- gen
    -- resultTypeName <- gen
    -- let resultType = MetaVar (resultName, MetaVar (resultTypeName, starType))
    let resultType = MetaVar (resultName, starType)
    formula <- translate c t resultType
    return (formula, resultType)

translate :: (MonadGen MetaVariableName m, Context c FreeVarName PiTermType) => c -> PiTerm -> H.Term -> m [Equation] -- m HouFormula
translate ctx t tType = case t of
  FreeVar (name, _) ->
    case IU.lookup ctx name of
      Nothing -> fail "definition of a variable was not found in the context"
      (Just ctxType) -> return [(tType, ctxType)] -- return $ Equation tType ctxType

  -- Metavar of some metavar type of [] type (proper type constructor)
  App t1 t2 _ -> do
    traceM "App"
    betaName <- gen
    let beta = (betaName, starType)
    let betaTerm = MetaVar beta
    vName <- gen
    -- vReturnName <- gen
    -- let vReturnType = MetaVar (vReturnName, starType)
    let vReturnType = starType
    let v = (vName, Abs betaTerm vReturnType)
    let vMetaVar = MetaVar v
    t1Formula <- translate ctx t1 vMetaVar
    t2Formula <- translate ctx t2 betaTerm
    t2WithTypes <- attachTypes t2
    return $ (tType, (App vMetaVar t2WithTypes vReturnType)) : t1Formula ++ t2Formula
      -- Exists betaType . Exists beta . Exists v $
      -- -- Exists beta . Exists v $
      --   And
      --     (Equation tType (App vMetaVar t2WithTypes starType))
      --     (And t1Formula t2Formula)

  Abs _ body -> do
    traceM "Abs"
    betaName <- gen
    let beta = (betaName, starType)
    let betaTerm = MetaVar beta
    vName <- gen
    -- vReturnName <- gen
    -- let vReturnType = MetaVar (vReturnName, starType)
    let vReturnType = starType
    let v = (vName, Abs betaTerm vReturnType)
    let vMetaVar = MetaVar v
    fvName <- gen
    let fv = FreeVar (fvName, betaTerm)
    (:) (tType, (Abs betaTerm (App vMetaVar (Var (0, betaTerm)) vReturnType))) <$>
      translate (IU.add ctx fvName betaTerm) (substitute fv 0 body) (App vMetaVar fv vReturnType)
    -- Exists betaType . Exists beta . Exists v .
    -- -- Exists beta . Exists v .
    --   And
    --     (Equation tType (Abs betaTerm (App vMetaVar (Var (0, betaTerm)) starType))) <$>
    --       translate (IU.add ctx fvName betaTerm) (substitute fv 0 body) (App vMetaVar betaTerm starType)

buildImplication :: Term -> Term -> Term
-- buildImplication t1 t2@(Abs arg t2b)
--   | getTermType t1 == starType, arg == t1,
--     getTermType t2b == starType =
--       Abs t1 (App t2 (Var (0, t1)) starType)
-- buildImplication t1 t2@(Abs arg t2b)
--   | getTermType t1 == starType, arg == t1,
--     getTermType t2b == starType =
--     t2
buildImplication t1 t2@(Abs arg t2b)
  | arg == t1 =
    t2
-- buildImplication t1 t2 | getTermType t1 == starType && getTermType t2 == Abs t1 starType =
--   let result = App
--         (App (Constant ("->", Abs starType (Abs (Abs (H.raise 1 t1) starType) starType))) t1 (Abs (Abs t1 starType) starType))
--         t2 starType
--   in trace ("build imlication: " ++ show result) result
-- buildImplication t1 t2 = traceStack "buildImplication" $ error $ "term: " ++ show t1 ++ "---" ++ show t2

-- TODO: General idea of the algorithm (the one presented below is rather not correct): Is it true
-- that if a term can be typed using dependent types then there exists an environment for simply
-- typed lambda calculus in which this term is also typable? If so, then before infering an
-- application, first try to typecheck both terms in some contexts. This also assures that every
-- term is strongly normalizable. Only then both are typable, try to infere a dependent type.
-- 1) infer all subterms using simply type lambda calculus
-- 2) if some subterm is not typable, then return an error
-- 3) otherwise, typcheck all types in the context, that is check if all types are correct and all
-- applications are correct. After this, substitute all dependent types of kind T -> * to kind
-- TermType -> *.
-- WARNING: you shouldn't forget their types this way. It makes it impossible to guess some
-- application of terms, or rather can make it non-normalizable.

attachTypes :: (MonadGen MetaVariableName m) => PiTerm -> m PiTerm
attachTypes t = do
  newTypeName <- gen
  let newType = MetaVar (newTypeName, starType)
  case t of
    MetaVar (name, _) -> return $ MetaVar (name, newType)
    Constant (name, _) -> return $ Constant (name, newType)
    Var (name, _) -> return $ Var (name, newType)
    FreeVar (name, _) -> return $  FreeVar (name, newType)
    App t1 t2 tType -> do
      (t1', t2') <- (,) <$> attachTypes t1 <*> attachTypes t2
      return $ App t1' t2' newType
    Abs _ body -> Abs newType <$> attachTypes body
    _ -> return t

solvePiTerm :: (Context c FreeVarName PiTermType) => c -> PiTerm -> [PiTermType]
solvePiTerm c = FML.toList . solve' c

solve' :: (Context c FreeVarName PiTermType) => c -> PiTerm -> FML.FMList PiTermType
-- solve' c t = iterDepthDefault $ do
--   (termType, equations) <- maybe failure return $ typeOf c t
--   solution <- unifyNonDeterministic equations createListSolution
--   result <- normalize $ apply solution termType
--   return result
solve' c t = iterDepthDefault $ do
  let (formula, resultType) = runTranslate c t
  solution <- unifyNonDeterministic formula createListSolution
  normalize $ apply solution resultType
