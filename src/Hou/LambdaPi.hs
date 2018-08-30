{-# LANGUAGE FlexibleContexts      #-}

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
import           Hou.MixedPrefix

import           Control.Monad
import           Control.Monad.Gen
import           Data.Maybe


typeOf :: (Context c FreeVarName TermType, MonadGen MetaVariableName m, MonadPlus m)
       => c
       -> Term
       -> m (TermType, [Equation])
typeOf c t = case t of
  FreeVar (varName, _) -> maybe mzero (\x -> return (x, [])) $ IU.lookup c varName
  App t1 t2 _ -> do
    (type1, c1) <- typeOf c t1
    (type2, c2) <- typeOf c t1
    case type1 of
      Pi from to -> return (substitute t2 0 to, [(from, type2)] `mappend` c1 `mappend` c2)
      _ -> do
        m1 <- gen
        let arg = MetaVar (m1, starType)
        m2 <- gen
        let result = MetaVar (m2, Pi arg starType)
        return (App result t2 starType,
                 [
                   (type1, Pi arg (App result (Var (0, arg)) starType)),
                   (type2, arg)
                 ] `mappend` c1 `mappend` c2
               )
  Abs _ body -> do
    freeVarName <- gen
    mvName <- gen
    let mv = MetaVar (mvName, starType)
    let fvVal = (freeVarName, mv)
    let fv = FreeVar fvVal
    (to, cs) <- typeOf (IU.add c freeVarName mv) (substitute fv 0 body)
    return (Pi mv (substituteFV (Var (0, mv)) fvVal (H.raise 1 to)), [(mv, mv)] `mappend` cs)
  _ -> mzero
