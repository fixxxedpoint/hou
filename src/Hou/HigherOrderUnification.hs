{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- TODO: implement Zaionc's remark regarding regular unification trees, e.g. fail if given a term of
-- the form ( X a ) = ( f ( X a )) we generate a term of the form ( H a ) = ( f ( H a )) (it
-- requires first order unification betweem equations). This way hou algorithm should also fail in
-- case of the first order unification for simply typed lambda terms - current version will loop in
-- case of a term \x . x x.

{-|
Module      : Hou.HigherOrderUnification
Description : Provides data types for representing isntances of the higher-order unification
              problem together with methods for solving it.
Copyright   : (c) 2018 Łukasz Lachowski <l.lachowski@gmail.com>
License     : MIT, see the file LICENSE
-}
module Hou.HigherOrderUnification(
  Term(..),
  TermType(..),
  MetaVariable,
  Equation,
  DeBruijnIndex,
  MetaVariableName,
  Solution(..),
  getTermType,
  someType,
  starType,
  preunifyAllSolutions,
  preunifyNonDeterministic,
  unifyAllSolutions,
  unifyNonDeterministic,
  createListSolution,
  normalize,
  getMetaVars,
  getMetavarId,
  getHead
  )
  where

import           Hou.Levels
import           Hou.Trace

import qualified Control.Applicative as Appl
import           Control.Arrow
import           Control.Monad
import           Control.Monad.Cont
import           Control.Monad.Gen
import qualified Data.FMList         as FML
import           Data.Foldable
import           Data.Maybe


type ConstantName = String

type DeBruijnIndex = Int

type MetaVariableName = Int

type MetaVariable = (MetaVariableName, TermType)

type Constant = (ConstantName, TermType)

type Variable = (DeBruijnIndex, TermType)

type VarTypeName = Int

data TermType =
  VarType VarTypeName |
  Implication TermType TermType
  deriving (Eq, Show)

starType :: TermType
starType = VarType 0

someType :: TermType
someType = VarType 1

data Term =
  MetaVar MetaVariable |
  Constant Constant |
  Var Variable |
  FreeVar Variable |
  App Term Term TermType |
  Abs TermType Term
  deriving (Eq, Show)

type Equation = (Term, Term)

{-|
Represents an abstract solution of the unification problem.
-}
class Solution s where
  add :: s -> MetaVariable -> Term -> s
  emptySolution :: s
  clearSolution :: s -> s
  clearSolution = const emptySolution
  apply :: s -> Term -> Term

newtype ListSolution = LS [(MetaVariable, Term)]

createListSolution :: ListSolution
createListSolution = LS []

instance Solution ListSolution where
  add (LS l) mv t = LS $ (mv, t) : l

  emptySolution = createListSolution

  apply (LS []) t = trace "1" t
  apply s (App t1 t2 appType) = trace "2" $ App (apply s t1) (apply s t2) appType
  apply s (Abs absType term) = trace "3" $ Abs absType $ apply s term
  apply (LS [(mv1, term)]) t@(MetaVar mv2) | mv1 == mv2 = trace "4.1" term
                                           | otherwise = trace "4.2" t
  apply (LS (s:rest)) t@(MetaVar _) = trace "5" $ apply (LS [s]) $ apply (LS rest) t
  apply _ t = trace "6" t

{-|
Preunification algorithm tries to solve a given list of equations, returning a solution when all of
the remaining equations are of the flex-flex form. It returns a list of possible solutions.
-}
preunifyAllSolutions :: (Solution s) => [Equation] -> s -> [s]
preunifyAllSolutions eqs s = FML.toList $ preunifyAllSolutions' eqs s

preunifyAllSolutions' :: (Solution s) => [Equation] -> s -> FML.FMList s
preunifyAllSolutions' eqs s = iterDepthDefault $ preunifyNonDeterministic eqs s

{-|
Preunification algorithm tries to solve a given list of equations, returning a solution when all of
the remaining equations are of the flex-flex form. It returns a non-deterministic computation
producing a list of possible solutions.
-}
preunifyNonDeterministic :: (Solution s, NonDet m, MonadPlus m, MonadCont m)
                         => [Equation] -> s -> m s
preunifyNonDeterministic eqs s =
  let nextEnum = toEnum . (1 +) . getMaxMetaVar $ eqs in
  trace "preunifyNonD..." $ runGenTFrom nextEnum $ preunify eqs s

preunify :: (Solution s, NonDet m, Appl.Alternative m, MonadGen MetaVariableName m, MonadCont m)
         => [Equation]
         -> s
         -> m s
preunify eqs s = let lnf = (toLongNormalForm *** toLongNormalForm) <$> eqs in
  preunify' lnf s

preunify' :: (Solution s, NonDet m, Appl.Alternative m, MonadGen MetaVariableName m, MonadCont m)
          => [Equation]
          -> s
          -> m s
preunify' [] solution = trace "preunify []" $ return solution
preunify' equations solution = interrupt $ callCC $ \exit -> do
  traceM $ "preunify: " ++ show equations
  simplified <- fixPointOfSimplify $ (normalize *** normalize) <$> equations
  traceM ("preunify2: " ++ show simplified)
  traceM ("preunify3: " ++ show (isSolved simplified))
  when (isSolved simplified) $ exit solution
  traceM "preunify4"
  let flexRigid = head . filter (\(a, b) -> isFlexible a && isRigid b) $ simplified
  (mv, term) <- generateStep flexRigid
  let (newSolution, newEquations) = update mv term solution simplified
  traceM ("preuniy5: " ++ show newEquations)
  preunify' newEquations newSolution

{-|
Completely unifies a list of equations. It returns a list of possible solutions.
-}
unifyAllSolutions :: (Solution s, NonDet m, Computation m)
                  => [Equation]
                  -> s
                  -> m s
unifyAllSolutions eqs s = iterDepthDefault $ unifyNonDeterministic eqs s

{-|
Completely unifies a list of equations. It returns a non-deterministic computation producing a list
of possible solutions.
-}
unifyNonDeterministic :: (Solution s, NonDet m, MonadPlus m, MonadCont m)
                      => [Equation]
                      -> s
                      -> m s
unifyNonDeterministic eqs s =
  let nextEnum = toEnum . (1 +) . getMaxMetaVar $ eqs in
  trace "preunifyF..." $ runGenTFrom nextEnum $ unify eqs s

unify :: (Solution s, NonDet m, Appl.Alternative m, MonadGen MetaVariableName m, MonadCont m)
      => [Equation]
      -> s
      -> m s
unify eqs s = do
  let lnf = (toLongNormalForm *** toLongNormalForm) <$> eqs
  presolution <- preunify lnf s
  traceM "already preunified"
  unify' ((apply presolution *** apply presolution) <$> lnf) presolution

unify' :: (Solution s, NonDet m, Appl.Alternative m, MonadGen MetaVariableName m, MonadCont m)
       => [Equation]
       -> s
       -> m s
unify' equations solution = interrupt $ callCC $ \exit -> do
  traceM ("unify: " ++ show equations)
  simplified <- fixPointOfSimplify $ (normalize *** normalize) <$> equations
  traceM ("unify2: " ++ show simplified)
  traceM ("unify3: " ++ show (isSolved simplified))
  when (null simplified) $ exit solution
  traceM $ "unify4: " ++ show simplified
  (mv, term) <- generateStep (head simplified)
  let (newSolution, newEquations) = update mv term solution simplified
  unify' newEquations newSolution

update :: (Solution s) => MetaVariable -> Term -> s -> [Equation] -> (s, [Equation])
update mv term solution eqs = do
  let thisSolution = add (clearSolution solution) mv term
  let newEquations = (apply thisSolution *** apply thisSolution) <$> eqs
  let newSolution = add solution mv term
  (newSolution, newEquations)

getMaxMetaVar :: [Equation] -> MetaVariableName
getMaxMetaVar eqs =
  maximum $ getMetavarId <$> concatMap getMetaVars [z | (x, y) <- eqs, z <- [x, y]]

getMetavarId :: MetaVariable -> MetaVariableName
getMetavarId (ix, _) = ix

getMetaVars :: Term -> [MetaVariable]
getMetaVars t = getMetaVars' t []
getMetaVars' :: Term -> [MetaVariable] -> [MetaVariable]
getMetaVars' (MetaVar metaVar) r = metaVar : r
getMetaVars' (App a b _) r       = getMetaVars' b $ getMetaVars' a r
getMetaVars' (Abs _ body) r      = getMetaVars' body r
getMetaVars' _ r                 = r

simplify :: (NonDet m, Appl.Alternative m, MonadGen MetaVariableName m) => Equation -> m [Equation]
simplify (t1, t2)
  | t1 == t2 = return [] -- check for metavars?
  | (Abs type1 a) <- t1,
    (Abs type2 b) <- t2,
    type1 == type2 = do
      newVar <- gen
      traceM $ "simplify Abs: " ++ show t1 ++ " --- " ++ show t2 ++ " --- " ++ show newVar
      let newCons = FreeVar (newVar, type1)
      let newA = substitute newCons 0 a
      let newB = substitute newCons 0 b
      traceM $ "simplify Abs2: " ++ show newA ++ " --- " ++ show newB
      simplify (newA, newB)
  | (c1, ctx1) <- getHead t1,
    (c2, ctx2) <- getHead t2,
    isFreeVarOrConstant c1 && isFreeVarOrConstant c2 = do
      traceM "simplify deeper"
      guard (c1 == c2) -- this can fail the whole process
      fold <$> mapM simplify (zip ctx1 ctx2) -- faster than using fixPointOfSimplify
  | isRigid t1 && isFlexible t2 = trace "rigid-flex" $ return [(t2, t1)]
  | isFlexible t1 && isRigid t2 = trace ("flex-rigid: " ++ show t1 ++ " --- " ++ show t2) $
                                    return [(t1, t2)]
  | isFlexible t1 && isFlexible t2 = trace "flex-flex" $ return [(t1, t2)]
  | otherwise = trace "otherwise" failure

fixPointOfSimplify :: (MonadGen MetaVariableName m, NonDet m, Appl.Alternative m)
                   => [Equation] -> m [Equation]
fixPointOfSimplify cs = do
  traceM $ "fixPointOfSimplify: " ++ show cs
  cs' <- fold <$> mapM simplify cs
  traceM $ "fixPointOfSimplify2: " ++ show cs'
  if cs' == cs then return cs else fixPointOfSimplify cs'

isFreeVarOrConstant :: Term -> Bool
isFreeVarOrConstant (FreeVar _)  = True
isFreeVarOrConstant (Constant _) = True
isFreeVarOrConstant _            = False

isRigid :: Term -> Bool
isRigid = not . isFlexible

isFlexible :: Term -> Bool
isFlexible t | (MetaVar _, _) <- getHead t = trace "is flexible" True
             | otherwise = False

isVarType :: TermType -> Bool
isVarType (VarType _) = True
isVarType _           = False

{-|
Tries to non-deterministically solve an equation using projection or imitation.
-}
generateStep :: (MonadGen MetaVariableName m, NonDet m, Appl.Alternative m)
             => Equation
             -> m (MetaVariable, Term)
generateStep (flex, rigid) | isFlexible flex = do
  let (flexTerm, _) = getHead flex
  flexVariable <- case flexTerm of
                   MetaVar var -> return var
                   _           -> failure
  let headConstant = getHeadConstant rigid
  let headFreeVar = getHeadFreeVar rigid
  let headMetaVar = getHeadMetaVar rigid
  let availableTerms = (Constant <$> maybeToList headConstant) ++
                       (FreeVar <$> maybeToList headFreeVar) ++
                       (MetaVar <$> maybeToList headMetaVar)
  traceM ("before generate: " ++ show headConstant)
  traceM $ "generateStep rigid: " ++ show rigid
  traceM $ "generateStep flex: " ++ show flex
  generatedTerm <- generate (getTermType flexTerm) availableTerms
  return (flexVariable, generatedTerm)

generate :: (MonadGen MetaVariableName m, NonDet m, Appl.Alternative m)
         => TermType
         -> [Term]
         -> m Term
generate varType availableTerms = do
  let (assumptions, goal) = getAssumptionsAndGoal varType
  let matchingAssumptions = getMatchingTerms goal $ Var <$> assumptions
  let matchingTerms = getMatchingTerms goal availableTerms
  traceM $ "matching var type: " ++ show varType
  traceM $ "Matching assumptions: " ++ show matchingAssumptions
  traceM $ "Matching terms: " ++ show matchingTerms
  traceM ("generate: " ++ show matchingAssumptions)
  head <- anyOf $ matchingAssumptions ++ matchingTerms
  traceM $ "generate head: " ++ show head ++ " --- " ++ show matchingAssumptions
                                          ++ " --- " ++ show matchingTerms
  result <- generateLongTerm assumptions head
  traceM ("generate result: " ++ show result)
  return $ toLongNormalForm result

generateLongTerm :: (MonadGen MetaVariableName m) => [Variable] -> Term -> m Term
generateLongTerm lambdas head = do
  traceM ("long term head: " ++ show head)
  body <- generateLongBody lambdas head
  traceM ("long term: " ++ show body)
  return $ Data.Foldable.foldr (Abs . getTermType . Var) body lambdas

generateLongBody :: (MonadGen MetaVariableName m) => [Variable] -> Term -> m Term
generateLongBody variables head =
  foldM newArgVar head $ getTermType . Var <$> trace ("assumptions: " ++ show assumptions) assumptions
  where
    (assumptions, _) = getAssumptionsAndGoal . getTermType $ head

    newArg tType = do
      newVar <- gen
      return $ MetaVar (newVar, tType)

    newArgVar body tType = do
      let newType = liftType tType
      newMetavar <- newArg newType
      traceM $ "newArgVar" ++ show tType
      let appliedMetavar =
            Data.Foldable.foldl
            (\a b -> App a b (shiftType . getTermType $ a))
            newMetavar
            (Var <$> variables)
      return $ App body appliedMetavar $ shiftType . getTermType $ body

    liftType tType = Data.Foldable.foldr Implication tType $ getTermType . Var <$> variables

    shiftType (Implication _ b) = b
    shiftType t                 = t

getAssumptionsAndGoal :: TermType -> ([Variable], TermType)
getAssumptionsAndGoal t =
  (Data.Foldable.foldr (\tType result -> (newDeBruijnIndex result, tType) : result) [] . init .
    Hou.HigherOrderUnification.foldr (:) [] $ t,
  getGoal t)
  where newDeBruijnIndex []          = 0
        newDeBruijnIndex ((ix, _):_) = ix + 1

getMatchingTerms :: TermType -> [Term] -> [Term]
getMatchingTerms goal = filter $ (goal ==) . getGoal . getTermType

getGoal :: TermType -> TermType
getGoal (Implication _ b) = getGoal b
getGoal g                 = g

foldr :: (TermType -> b -> b) -> b -> TermType -> b
foldr fun initValue (Implication a b) = fun a $ Hou.HigherOrderUnification.foldr fun initValue b
foldr fun initValue v@(VarType _) = fun v initValue

isSolved :: [Equation] -> Bool
isSolved [] = True
isSolved equations = trace "solved" $ and $ uncurry (&&) . (isFlexible *** isFlexible) <$> equations

substitute :: Term -> DeBruijnIndex -> Term -> Term
substitute new index term = case term of
  v@(Var (deBruijnIndex, varType)) -> case compare deBruijnIndex index of
    LT -> v
    EQ -> new
    GT -> Var (deBruijnIndex-1, varType)
  App a b termType -> App (substitute new index a) (substitute new index b) termType
  Abs termType a -> Abs termType (substitute (raise 1 new) (index+1) a)
  _ -> term

raise :: Int -> Term -> Term
raise = raise' 0
  where raise' lower by t = case t of
          v@(Var (deBruijnIndex, varType)) -> if deBruijnIndex >= lower
                                                then Var (by + deBruijnIndex, varType)
                                                else v
          App l r tType -> App (raise' lower by l) (raise' lower by r) tType
          Abs varType body -> Abs varType (raise' (lower + 1) by body)
          v -> v

toLongNormalForm :: Term -> Term
toLongNormalForm t =
  let result = normalize . toLongNormalForm' . normalize $ t in
  result

toLongNormalForm' :: Term -> Term
toLongNormalForm' (Abs tType body) = Abs tType $ toLongNormalForm' body
toLongNormalForm' (App t1 t2 termType) = App (toLongNormalForm' t1) (toLongNormalForm' t2) termType
toLongNormalForm' v = do
  let (assumptions, _) = getAssumptionsAndGoal . getTermType $ v
  let newVar = case v of
        Var (ix, termType) -> Var (ix + length assumptions, termType)
        _                  -> v
  let body =
        Data.Foldable.foldl
        (\b a -> let (Implication _ tType) = getTermType b in App b (toLongNormalForm' a) tType)
        newVar
        (Var <$> assumptions)
  Data.Foldable.foldr (\a b -> Abs (getTermType a) b) body $ Var <$> assumptions

normalize :: Term -> Term
normalize t = case t of
  App l r tType -> case normalize l of
    Abs _ body -> normalize (substitute (normalize r) 0 body)
    l'         -> App l' (normalize r) tType
  Abs varType body -> Abs varType $ normalize body
  v -> v

getHead :: Term -> (Term, [Term])
getHead t = get t []
  where get (App a b _) ctx = get a (b : ctx)
        get tt          ctx = (tt, ctx)

getHeadConstant :: Term -> Maybe Constant
getHeadConstant t = case t of
  Constant constant -> Just constant
  App m _ _         -> getHeadConstant m
  _                 -> Nothing

getHeadFreeVar :: Term -> Maybe Variable
getHeadFreeVar t = case t of
  FreeVar var -> Just var
  App m _ _   -> getHeadFreeVar m
  _           -> Nothing

getHeadMetaVar :: Term -> Maybe MetaVariable
getHeadMetaVar t = case t of
  MetaVar var -> Just var
  App m _ _   -> getHeadMetaVar m
  _           -> Nothing

getTermType :: Term -> TermType
getTermType (MetaVar (_, t))  = t
getTermType (Constant (_, t)) = t
getTermType (Var (_, t))      = t
getTermType (FreeVar (_, t))  = t
getTermType (App _ _ t)       = t
getTermType (Abs t body)      = Implication t $ getTermType body

isLongNormalForm :: Term -> Bool
isLongNormalForm t = case getTermType t of
  VarType _ -> do
    let (head, apps) = getHead t
    case head of
      Abs _ _ -> False
      _       -> and $ isLongNormalForm <$> apps
  Implication t1 t2 -> case t of
    Abs _ t3 -> isLongNormalForm t3
    _        -> False
