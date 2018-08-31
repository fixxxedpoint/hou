{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-|
Module      : Hou.MixedPrefix
Description : Provides a method of translating instances of the higher-order unification problem
              with possible mixed quantifiers onto basic version of the higher-order unification. It
              is based on the article "Unification Under a Mixed Prefix" of Dale Miller
              <http://www.lix.polytechnique.fr/~dale/papers/jsc92.pdf>.
Copyright   : (c) 2018 Łukasz Lachowski <l.lachowski@gmail.com>
License     : MIT, see the file LICENSE
-}
module Hou.MixedPrefix(
  HouFormula(..),
  PrenexNormalForm(..),
  Quantifier(..),
  RaisedNormalForm(..),
  solve,
  solveNonDeterministic,
  toPrenexNormalForm,
  Hou.MixedPrefix.raise,
  toEquation
  )
  where

import           Hou.HigherOrderUnification as H
import           Hou.Levels
import           Hou.Trace

import           Control.Arrow
import           Control.Monad
import           Control.Monad.Gen
import qualified Data.FMList                as FML
import           Data.Functor.Identity
import           Prelude                    hiding (head)

{-|
Represents a formula of higher-order unification with possible mixed quantifiers.
-}
data HouFormula =
  Equation H.Term H.Term |
  And HouFormula HouFormula |
  Exists MetaVariable HouFormula |
  ForAll MetaVariable HouFormula
  deriving (Eq, Show)

data Quantifier = QExists MetaVariable | QForAll MetaVariable deriving (Show, Eq)

data PrenexNormalForm = PNF { head :: [Quantifier], body :: [H.Equation] } deriving (Show, Eq)

data RaisedNormalForm = RNF { exists :: [MetaVariable], forall :: [MetaVariable], eqs :: [H.Equation] } deriving (Show, Eq)

toPrenexNormalForm :: HouFormula -> PrenexNormalForm
toPrenexNormalForm form =
  let (q, eq) = collect form [] [] in
  PNF { head = reverse q, body = reverse eq }
  where
    collect :: HouFormula -> [Quantifier] -> [H.Equation] -> ([Quantifier], [H.Equation])
    collect formula q eq = case formula of
      (Equation t1 t2) -> (q, (t1, t2) : eq)
      (And f1 f2) ->
        let (q1, e2) = collect f1 q eq in
        collect f2 q1 e2
      (Exists var f) -> collect f (QExists var : q) eq
      (ForAll var f) -> collect f (QForAll var : q) eq

-- TODO: for sake of simplicity consider to just use the fixed-point strategy
raise :: (Solution s) => PrenexNormalForm -> s -> (RaisedNormalForm, s)
raise f@PNF { body = b } s =
  let nextEnum = toEnum . (1 +) . maximum $ concatMap getMetaFreeVars [z | (x, y) <- b, z <- [x, y]] in
  runGenFrom nextEnum $ raise' f [] [] s

raise' :: (MonadGen DeBruijnIndex m, Solution s) => PrenexNormalForm -> [MetaVariable] -> [MetaVariable] -> s -> m (RaisedNormalForm, s)
raise' (PNF (QExists var : rest) body) [] exists s =
  raise' (PNF rest body) [] (var : exists) s
  -- return (RNF (var : exists result) (forall result) (eqs result), s')
  -- return (result { exists = var : exists result }, s')
raise' (PNF (QForAll var : rest) body) forall exists s =
  raise' (PNF rest body) (var : forall) exists s
raise' (PNF (QExists var : rest) body) forall exists s = do
  let varType = getTermType $ MetaVar var
  let newType = foldl (\b a -> Pi (getTermType $ MetaVar a) b) varType forall
  newMetavarName <- gen
  let newMetavar = (newMetavarName, newType)
  let newVar = foldr (\a b -> let (Pi _ r) = getTermType b in App b a r) (MetaVar newMetavar) $ MetaVar <$> forall
  let newSubstitution = add s var newVar
  raise' (PNF rest body) forall (newMetavar : exists) newSubstitution
raise' (PNF [] body) forall exists s = do
  let fixed = (apply s *** apply s) <$> body
  return (RNF (reverse exists) (reverse forall) fixed, s)

abstractMetavariable :: MetaVariable -> Term -> Term
abstractMetavariable mv t = Abs (getTermType $ MetaVar mv) $ switchMetavarToVar mv t

switchMetavarToVar :: MetaVariable -> Term -> Term
switchMetavarToVar = switchMetavarToVar' 0

switchMetavarToVar':: DeBruijnIndex -> MetaVariable -> Term -> Term
switchMetavarToVar' ix v@(varIndex, varType) term =
  case term of
    (MetaVar (termIndex, _)) | termIndex == varIndex -> Var (ix, varType)
                             | otherwise -> term
    (App t1 t2 tType) -> App (switchMetavarToVar' ix v t1) (switchMetavarToVar' ix v t2) tType
    (Abs tType t) -> Abs tType (switchMetavarToVar' (ix+1) v t)
    _ -> term

{-|
Translates a formula in raised normal form onto a single equation of the higher-order
unification problem.
-}
toEquation :: RaisedNormalForm -> Equation
toEquation RNF { exists = e, forall = f, eqs = eq } = runIdentity $ do
  let zReturnType = someType
  let zType = foldr Pi zReturnType $ (getTermType . fst) <$> eq
  let zVar = Var (0, zType)

  let bodyBuilder = foldl (\b a -> let (Pi _ bT) = getTermType b in App b a bT) zVar
  let m1 = bodyBuilder $ fst <$> eq
  let m2 = bodyBuilder $ snd <$> eq

  let lambdaBuilder for m = trace ("lambdas: " ++ show m) $ foldr abstractMetavariable m for
  let appBuilder terms m = trace ("builder2: " ++ show m) $ foldl (\b a -> let (Pi _ bT) = getTermType b in trace ("builder: " ++ show (getTermType b)) $ App b a bT) m $ MetaVar <$> terms
  let resultBuilder es fs = appBuilder es . lambdaBuilder es . lambdaBuilder fs . Abs zType

  let m1Result = resultBuilder e f m1
  let m2Result = resultBuilder e f m2

  traceM $ "toEquation zType:" ++ show zType
  traceM $ "toEquation result:" ++ show m1Result ++ " --- " ++ show m2Result
  return (m1Result, m2Result)

{-|
Tries to solve a given instance of the higher-order unification with mixed quantifiers. It returns
a first solution that was found by the search strategy.
-}
solve :: (Solution s) => HouFormula -> s -> s
solve f s = FML.head . iterDepthDefault $ solveNonDeterministic f s

{-|
Given an instance of the higher-order unification with mixed quantifiers it returns
a non-deterministic computation that tries to solve a given formula.
-}
solveNonDeterministic :: (Solution s, NonDet n) => HouFormula -> s -> NonDeterministicT r n s
solveNonDeterministic f s = do
  let prenexNormalForm = toPrenexNormalForm f
  let (raised, s') = Hou.MixedPrefix.raise prenexNormalForm s
  let equation = toEquation raised
  traceM $ "solveNonDeterministic 1: " ++ show prenexNormalForm
  traceM $ "solveNonDeterministic 2: " ++ show equation
  traceM $ "solveNonDeterministic 3: " ++ show raised
  solved <- unifyNonDeterministic [equation] s'
  return solved
