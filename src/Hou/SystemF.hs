{-# LANGUAGE FlexibleContexts      #-}

{-|
Module      : Hou.SystemF
Description : Provides methods for type checking and type inferencing of types for terms of SystemF.
Copyright   : (c) 2018 Łukasz Lachowski <l.lachowski@gmail.com>
License     : MIT, see the file LICENSE
-}
module Hou.SystemF(
  VarName,
  FTermType(..),
  Name,
  FTerm(..),
  inferType,
  inferTypes,
  toTermType
  ) where

import qualified Hou.HigherOrderUnification as H
import           Hou.InferenceUtils         as IU
import           Hou.Levels
import           Hou.MixedPrefix            as M
import           Hou.Trace

import           Control.Monad.Gen
import           Data.FMList                as FML
import           Data.List
import           Data.Maybe
import qualified Debug.Trace


type VarName = Int

{-|
Represents type a term of SystemF.
-}
data FTermType =
  VarType VarName |
  Implication FTermType FTermType |
  ForAll VarName FTermType
  deriving (Show, Read, Eq)

{-|
Represents terms of SystemF.
-}
data FTerm =
  Var Name (Maybe FTermType) |
  App FTerm FTerm |
  TypeApp FTerm (Maybe FTermType) |
  Abs Name (Maybe FTermType) FTerm |
  TypeAbs (Maybe VarName) FTerm
  deriving (Show, Read, Eq)

implication :: H.Term -> H.Term -> H.Term
implication t1 t2 | H.getTermType t1 == H.starType && H.getTermType t2 == H.starType =
  H.App
  (H.App (H.Constant ("->", H.Abs H.starType (H.Abs H.starType H.starType))) t1 (H.Abs H.starType H.starType))
  t2 H.starType

forAll :: H.Term -> H.Term
forAll t | H.getTermType t == H.Abs H.starType H.starType = H.App (H.Constant ("∀", H.Abs (H.Abs H.starType H.starType) H.starType)) t H.starType

{-|
Function returning first valid type found for a given term.
-}
inferType :: FTerm -> FTermType
inferType = Data.List.head . inferTypes

{-|
If a given term is typable, it returns an infinite list of possible typings for it.
-}
inferTypes :: FTerm -> [FTermType]
inferTypes = FML.toList . inferTypes'

inferTypes' :: FTerm -> FML.FMList FTermType
inferTypes' nterm = iterDepthDefault $ do
  term <- anyOf $ termToFTerms nterm
  solution <- inferFTerm term
  return solution

inferFTerm :: (NonDet n) => FTerm -> NonDeterministicT r n FTermType
inferFTerm t = trace ("inferFTerm: " ++ show t) $ do
  let (fixedFormula, resultType) = prepareFormula t
  traceM $ "inferFTerm 1: " ++ show fixedFormula
  solution <- solveNonDeterministic fixedFormula H.createListSolution
  traceM $ "inferFTerm 2: " ++ show resultType
  -- Debug.Trace.traceM $ "inferFTerm 3: " ++ show (H.normalize $ H.apply solution resultType)
  toFTermType <$> (H.normalize $ H.apply solution resultType)
  -- return $ toFTermType (H.normalize $ H.apply solution resultType)

{-|
Maps a typing problem of a term of SystemF onto a formula of higher-order unification.
-}
prepareFormula :: FTerm   -- ^ A term with possible type annotations.
  -> (HouFormula, H.Term) -- ^ Typing of the term encoded as a formula of higher-order unification
                          --   and a term that represents its type.
prepareFormula t = runGen $ do
  termType <- newMetaVariable
  let resultType = H.MetaVar termType
  let ctx = createMapContext
  formula <- translate ctx t resultType
  let fixedFormula = Exists termType formula
  return (fixedFormula, resultType)

newMetaVariable :: (MonadGen H.MetaVariableName m) => m H.MetaVariable
newMetaVariable = do
  newVar <- gen
  return (newVar, H.starType)

{-|
Main function of this module. It translates a problem of typing of a term of SystemF  onto
the problem of higher-order unification.
-}
translate :: (MonadGen H.MetaVariableName m, Context c Name H.Term) => c -> FTerm -> H.Term -> m HouFormula
translate ctx t tType = case t of
  (Var name termType) ->
    case IU.lookup ctx name of
      Nothing -> fail "definition of a variable was not found in the context"
      (Just ctxType) ->
        case termType of
          (Just termTypeVal) -> return $ And (Equation tType ctxType) (Equation tType $ toTermType termTypeVal)
          _ -> return $ Equation tType ctxType

  (App t1 t2) -> do
    v <- newMetaVariable
    let vMetaVar = H.MetaVar v
    t1Form <- translate ctx t1 $ implication vMetaVar tType
    t2Form <- translate ctx t2 vMetaVar
    return $ Exists v $ And t1Form t2Form

  (Abs name termType term) -> do
    beta <- newMetaVariable
    let betaTerm = fromMaybe (H.MetaVar beta) $ toTermType <$> termType
    v <- newMetaVariable
    let vMetaVar = H.MetaVar v
    Exists beta . Exists v .
      And
        (Equation tType (implication betaTerm vMetaVar)) <$>
        translate (add ctx name betaTerm) term vMetaVar

  (TypeApp term termType) -> do
    beta <- newMetaVariable
    let betaTerm = fromMaybe (H.MetaVar beta) $ toTermType <$> termType
    vName <- gen
    let v = (vName, H.Abs H.starType H.starType)
    let vMetaVar = H.MetaVar v
    Exists beta . Exists v .
      And
        (Equation tType (H.App vMetaVar betaTerm H.starType)) <$>
        translate ctx term (forAll vMetaVar)

  (TypeAbs name term) -> do
    newVar <- gen
    let v = (newVar, H.Abs H.starType H.starType)
    let vMetaVar = H.MetaVar v
    phi <- fromMaybe newMetaVariable $ (\n -> return (n, H.starType)) <$> name
    Exists v .
      And (Equation tType (forAll vMetaVar)) .
      M.ForAll phi <$> translate ctx term (H.App vMetaVar (H.MetaVar phi) H.starType)

termToFTerms :: FTerm -> [FTerm]
termToFTerms = injectQuantifiers

{-|
For a given term it outputs an infinite list of terms created by injecting the ForAll and
TypeApp annotations. Returned list is sorted by the size.
-}
injectQuantifiers :: FTerm -> [FTerm]
injectQuantifiers t = t : injectQuantifiers' [t]

injectQuantifiers' :: [FTerm] -> [FTerm]
injectQuantifiers' previous =
  let this = concatMap injectQuantifier previous
  in
  this ++ injectQuantifiers' this

injectQuantifier :: FTerm -> [FTerm]
injectQuantifier t =
  let next = case t of
        (App t1 t2) -> [ App t1' t2 | t1' <- injectQuantifier t1 ] ++ [ App t1 t2' | t2' <- injectQuantifier t2 ]
        (TypeApp term tType) -> [TypeApp term' tType | term' <- injectQuantifier term]
        (Abs name tType term) -> [Abs name tType term' | term' <- injectQuantifier term]
        (TypeAbs tType term) -> [TypeAbs tType term' | term' <- injectQuantifier term]
        _ -> []
  in
  [TypeApp t Nothing, TypeAbs Nothing t] ++ next

toFTermType :: H.Term -> FTermType
toFTermType t = trace ("toFTermType: " ++ show t) $
  let freeVarsCount = countFreeAndMetaVars t
  in
  runGenFrom (freeVarsCount + 1) . toFTermType' [] $ t

countFreeAndMetaVars :: H.Term -> Int
countFreeAndMetaVars t = case t of
  (H.MetaVar _)   -> 1
  (H.FreeVar _)   -> 1
  (H.App t1 t2 _) -> countFreeAndMetaVars t1 + countFreeAndMetaVars t2
  (H.Abs _ term)  -> countFreeAndMetaVars term
  _               -> 0

toFTermType' :: (MonadGen VarName m) => [VarName] -> H.Term -> m FTermType
toFTermType' lambdas t = case t of
  -- TODO: this removes the need for unify, FreeVars and MetaVars should have different names
  (H.MetaVar (ix, _)) -> return $ VarType ix
  (H.Var (ix, _)) -> return $ VarType $ lambdas !! ix
  (H.FreeVar (ix, _)) -> return $ VarType ix
  (H.App (H.App (H.Constant ("->", _)) a _) b _) ->
    trace "toFTermType ->" $ Implication <$> toFTermType' lambdas a <*> toFTermType' lambdas b
  (H.App (H.Constant ("∀", _)) term _) -> trace "toFTermType 'forall'" $ toFTermType' lambdas term
  (H.Abs _ term) -> do
    newBoundVariable <- gen
    let lambdas' = newBoundVariable : lambdas
    Hou.SystemF.ForAll newBoundVariable <$> toFTermType' lambdas' term
  _ -> fail $ "I don't know what happend. Processed term: "  ++ show t

{-|
Translates a type of SystemF onto a simply typed lambda term.
-}
toTermType :: FTermType -> H.Term
toTermType t = trace ("toTermType: " ++ show t) $ toTermType' [] t

toTermType' :: [VarName] -> FTermType -> H.Term
toTermType' bounded t = trace ("toTermType' 1: " ++ show t) $ case t of
  (VarType name) -> case elemIndex name bounded of
    (Just ix) -> H.Var (ix, H.starType)
    Nothing -> trace ("toTermType': " ++ show name) $ H.FreeVar (name, H.starType)
  (Implication t1 t2) -> implication (toTermType' bounded t1) (toTermType' bounded t2)
  (Hou.SystemF.ForAll name term) -> forAll $ H.Abs H.starType $ toTermType' (name:bounded) term
