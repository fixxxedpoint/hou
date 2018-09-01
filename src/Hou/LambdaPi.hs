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

typeOf :: (Context c FreeVarName PiTermType)
       => c
       -> PiTerm
       -> Maybe (PiTermType, [Equation])
typeOf c t = do
  let genEnum = toEnum . (1 +) . maximum . (:) 0 . getMetaFreeVars $ t
  runGenTFrom genEnum $ typeOf' c t


typeOf' :: (Context c FreeVarName PiTermType, MonadGen MetaVariableName m, MonadPlus m)
       => c
       -> PiTerm
       -> m (PiTermType, [Equation])
typeOf' c t = case t of
  FreeVar (varName, _) -> trace ("free" ++ show varName) $ maybe mzero (\x -> trace ("typ: " ++ show x) $ return (x, [])) $ IU.lookup c varName
  -- App t1 t2 _ -> do
  --   (type1, c1) <- typeOf c t1
  --   (type2, c2) <- typeOf c t2
  --   case type1 of
  --     Pi from to -> trace ("asdasd") $ return (substitute t2 0 to, [(from, type2)] `mappend` c1 `mappend` c2)
  --     _ -> do
  --       traceM "o co cho?"
  --       m1 <- gen
  --       let arg = MetaVar (m1, starType)
  --       m2 <- gen
  --       let result = MetaVar (m2, Pi arg starType)
  --       return (App result t2 starType,
  --                [
  --                  (type1, Pi arg (App result (Var (0, arg)) starType)),
  --                  (type2, arg)
  --                ] `mappend` c1 `mappend` c2
  --              )
  App t1 t2 _ -> do
    (type1, c1) <- typeOf' c t1
    (type2, c2) <- typeOf' c t2
    case type1 of
      Abs from to -> trace ("asdasd") $ return (substituteWT t2 0 to, [(from, type2)] `mappend` c1 `mappend` c2)
      _ -> do
        traceM "o co cho?"
        m1 <- gen
        -- m1Result <- gen
        let arg = MetaVar (m1, starType) -- MetaVar (m1Result, starType))
        m2 <- gen
        m3 <- gen
        -- m3Result <- gen
        let returnType = MetaVar (m3, starType) -- MetaVar (m3Result, starType))
        let result = MetaVar (m2, Abs arg returnType)
        return (App result t2 starType,
                 [
                   (type1, Abs arg (App result (Var (0, arg)) returnType)),
                   (type2, arg)
                 ] `mappend` c1 `mappend` c2
               )
  -- Abs _ body -> do
  --   freeVarName <- gen
  --   mvName <- gen
  --   let mv = MetaVar (mvName, starType)
  --   let fvVal = (freeVarName, mv)
  --   let fv = FreeVar fvVal
  --   (to, cs) <- typeOf (IU.add c freeVarName mv) (substitute fv 0 body)
  --   return (Pi mv (substituteFV (Var (0, mv)) fvVal (H.raise 1 to)), [(mv, mv)] `mappend` cs)
  Abs _ body -> do
    freeVarName <- gen
    mvName <- gen
    let mv = MetaVar (mvName, starType)
    let fvVal = (freeVarName, mv)
    let fv = FreeVar fvVal
    (to, cs) <- typeOf' (IU.add c freeVarName mv) (substituteWT fv 0 body)
    return (Abs mv (substituteFV (Var (0, mv)) fvVal (H.raise 1 to)), [(mv, mv)] `mappend` cs)
  _ -> mzero

solvePiTerm :: (Context c FreeVarName PiTermType) => c -> PiTerm -> [PiTermType]
solvePiTerm c = FML.toList . solve' c

solve' :: (Context c FreeVarName PiTermType) => c -> PiTerm -> FML.FMList PiTermType
solve' c t = do
  (termType, equations) <- maybe mzero return $ typeOf c t
  -- traceM $ show termType
  -- traceM "---"
  -- traceM $ show equations
  iterDepthDefault $ do
    solution <- unifyNonDeterministic equations createListSolution
    return $ normalize $ apply solution termType
