{-# LANGUAGE FlexibleContexts      #-}

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
  FreeVarName,
  Solution(..),
  getTermType,
  someType,
  starType,
  varType,
  preunifyAllSolutions,
  preunifyNonDeterministic,
  unifyAllSolutions,
  unifyNonDeterministic,
  createListSolution,
  normalize,
  getMetaFreeVars,
  getMetavarId,
  getHead,
  substitute,
  substituteFV,
  raise
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

import qualified Debug.Trace


type ConstantName = String

type DeBruijnIndex = Int

type MetaVariableName = Int

type FreeVarName = MetaVariableName

type VarTypeName = Int

type MetaVariable = (MetaVariableName, TermType)

type Constant = (ConstantName, TermType)

type Variable = (DeBruijnIndex, TermType)

type FreeVariable = (FreeVarName, TermType)

starType :: TermType
starType = Constant ("*", Constant ("[]", Uni))

someType :: TermType
someType = Constant ("a", starType)

varType :: Int -> TermType
varType name = FreeVar (name, Uni)

data Term =
  MetaVar MetaVariable |
  Constant Constant |
  Var Variable |
  FreeVar FreeVariable |
  App Term Term TermType |
  Abs TermType Term |
  Uni
  deriving (Eq, Read, Show)

type TermType = Term

type Equation = (Term, Term)

{-|
Represents an abstract solution of the unification problem.
-}
class (Show s) => Solution s where
  add :: s -> MetaVariable -> Term -> s
  emptySolution :: s
  clearSolution :: s -> s
  clearSolution = const emptySolution
  apply :: s -> Term -> Term

newtype ListSolution = LS [(MetaVariable, Term)] deriving (Show)

createListSolution :: ListSolution
createListSolution = LS []

instance Solution ListSolution where
  add (LS l) mv t = LS $ (mv, t) : l

  emptySolution = createListSolution

  apply (LS []) t = trace "1" t
  apply s (App t1 t2 appType) = trace "2" $ App (apply s t1) (apply s t2) appType
  apply s (Abs absType term) = trace "3" $ Abs absType $ apply s term
  apply s@(LS [(mv1@(mv1Name, _), term)]) t@(MetaVar mv2@(mv2Name, tType)) | mv1Name == mv2Name = trace "5.1" term
                                                                           | otherwise = trace "5.2" t
  apply (LS (s:rest)) t@(MetaVar _) = trace "6" $ apply (LS [s]) $ apply (LS rest) t
  apply _ t = trace "7" t

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
preunifyNonDeterministic :: (Solution s, NonDet n) => [Equation] -> s -> NonDeterministicT r n s
preunifyNonDeterministic eqs s =
  let nextEnum = toEnum . (1 +) . getMaxMetaFreeVar $ eqs in
  trace "preunifyNonD..." $ runGenTFrom nextEnum $ preunify eqs s

preunify :: (Solution s, NonDet n)
         => [Equation]
         -> s
         -> GenT MetaVariableName (NonDeterministicT r n) s
preunify eqs s = let lnf = (toLongNormalForm *** toLongNormalForm) <$> eqs in
  preunify' lnf s

preunify' :: (Solution s, NonDet n)
          => [Equation]
          -> s
          -> GenT MetaVariableName (NonDeterministicT r n) s
preunify' [] solution = trace "preunify []" $ return solution
preunify' equations solution = interrupt $ callCC $ \exit -> do
  simplified <- fixPointOfSimplify $ (normalize *** normalize) <$> equations
  when (isSolved simplified) $ exit solution
  let flexRigid = head . filter (\(a, b) -> isFlexible a && isRigid b) $ simplified
  (mv, term) <- generateStep flexRigid
  let (newSolution, newEquations) = update mv term solution simplified
  preunify' newEquations newSolution

{-|
Completely unifies a list of equations. It returns a list of possible solutions.
-}
unifyAllSolutions :: (Solution s, NonDet m, Computation m, MonadPlus m)
                  => [Equation]
                  -> s
                  -> m s
unifyAllSolutions eqs s = iterDepthDefault $ unifyNonDeterministic eqs s

{-|
Completely unifies a list of equations. It returns a non-deterministic computation producing a list
of possible solutions.
-}
unifyNonDeterministic :: (Solution s, NonDet n)
                      => [Equation]
                      -> s
                      -> NonDeterministicT r n s
unifyNonDeterministic eqs s =
  let nextEnum = toEnum . (1 +) . getMaxMetaFreeVar $ eqs in
  trace "preunifyF..." $ runGenTFrom nextEnum $ unify eqs s

unify :: (Solution s, NonDet n)
      => [Equation]
      -> s
      -> GenT MetaVariableName (NonDeterministicT r n) s
unify eqs s = do
  let lnf = (toLongNormalForm *** toLongNormalForm) <$> eqs
  presolution <- preunify lnf s
  traceM "already preunified"
  unify' ((apply presolution *** apply presolution) <$> lnf) presolution

unify' :: (Solution s, NonDet n)
       => [Equation]
       -> s
       -> GenT MetaVariableName (NonDeterministicT r n) s
unify' equations solution = interrupt $ callCC $ \exit -> do
  simplified <- fixPointOfSimplify $ (normalize *** normalize) <$> equations
  traceM ("unify3: " ++ show (isSolved simplified))
  when (null simplified) $ exit solution
  (mv, term) <- generateStep (head simplified)
  let (newSolution, newEquations) = update mv term solution simplified
  unify' newEquations newSolution

update :: (Solution s) => MetaVariable -> Term -> s -> [Equation] -> (s, [Equation])
update mv term solution eqs = do
  let thisSolution = add (clearSolution solution) mv term
  let newEquations = (apply thisSolution *** apply thisSolution) <$> eqs
  let newSolution = add solution mv term
  -- FIXME: verify this
  -- (newSolution, (getTermType (MetaVar mv), getTermType term) : newEquations)
  (newSolution, newEquations)

getMaxMetaFreeVar :: [Equation] -> MetaVariableName
getMaxMetaFreeVar eqs =
  maximum . (:) 0 $ concatMap getMetaFreeVars [z | (x, y) <- eqs, z <- [x, y]]

getMetavarId :: MetaVariable -> MetaVariableName
getMetavarId (ix, _) = ix

getMetaFreeVars :: Term -> [MetaVariableName]
getMetaFreeVars t = getMetaFreeVars' t []
getMetaFreeVars' :: Term -> [MetaVariableName] -> [MetaVariableName]
getMetaFreeVars' (MetaVar (metaVar, _)) r = metaVar : r
getMetaFreeVars' (FreeVar (freeVar, _)) r = freeVar : r
getMetaFreeVars' (App a b _) r       = getMetaFreeVars' b $ getMetaFreeVars' a r
getMetaFreeVars' (Abs _ body) r      = getMetaFreeVars' body r
getMetaFreeVars' _ r                 = r

simplify :: (MonadPlus m, MonadGen MetaVariableName m) => Equation -> m [Equation]
simplify (t1, t2)
  | t1 == t2 = return [] -- check for metavars?
  | (Abs type1 a) <- t1,
    (Abs type2 b) <- t2 = do
    -- type1 == type2 = do
      newVar <- gen
      let newCons = FreeVar (newVar, type1)
      let newA = substitute newCons 0 a
      let newB = substitute newCons 0 b
      simplify (newA, newB)
      -- return [(newA, newB)]
  | (c1, ctx1) <- getHead t1,
    (c2, ctx2) <- getHead t2,
    isFreeVarOrConstant c1 && isFreeVarOrConstant c2 = do
      guard (c1 == c2) -- this can fail the whole process
      fold <$> mapM simplify (zip ctx1 ctx2) -- faster than using fixPointOfSimplify
  | isRigid t1 && isFlexible t2 = trace "rigid-flex" $ return [(t2, t1)]
  -- | isFlexible t1 && isRigid t2 = Debug.Trace.trace ("flex-rigid: " ++ show t1 ++ " --- " ++ show t2) $ return [(getTermType t1, getTermType t2), (t1, t2)]
  | isFlexible t1 && isRigid t2 = trace ("flex-rigid: " ++ show t1 ++ " --- " ++ show t2) $ return [(t1, t2)]
  | isFlexible t1 && isFlexible t2 = trace "flex-flex" $ return [(t1, t2)]
  | otherwise = trace ("otherwise: " ++ show t1 ++ "---" ++ show t2) mzero

fixPointOfSimplify :: (MonadPlus m, MonadGen MetaVariableName m) => [Equation] -> m [Equation]
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
isVarType (Abs _ _) = False
isVarType _           = True

{-|
Tries to non-deterministically solve an equation using projection or imitation.
-}
generateStep :: (MonadPlus m, MonadGen MetaVariableName m)
             => Equation
             -> m (MetaVariable, Term)
generateStep (flex, rigid) | isFlexible flex = do
  let (flexTerm, _) = getHead flex
  flexVariable <- case flexTerm of
                   (MetaVar var) -> return var
                   _             -> mzero
  let headConstant = getHeadConstant rigid
  let headFreeVar = getHeadFreeVar rigid
  let headMetaVar = getHeadMetaVar rigid
  -- FIXME: add possibility to generate a lambda abstraction
  let availableTerms = (Constant <$> maybeToList headConstant) ++
                       (FreeVar <$> maybeToList headFreeVar) ++
                       (MetaVar <$> maybeToList headMetaVar)
  -- TODO add posibility to return a Pi term
  traceM $ "before generate: " ++ show headConstant
  -- Debug.Trace.traceM $ "before generate: " ++ show headConstant
  -- Debug.Trace.traceM $ "generateStep rigid: " ++ show rigid
  -- Debug.Trace.traceM $ "generateStep flex: " ++ show flex
  generatedTerm <- generate (getTermType flexTerm) availableTerms
  -- Debug.Trace.traceM $ "generated term: " ++ show flexVariable ++ "---" ++ show generatedTerm
  return (flexVariable, generatedTerm)
-- generateStep (t1, t2) = fail $ "first term of the equation is not flexible: " ++ show t1 ++ "---" ++ show t2
generateStep (t1, t2) = Debug.Trace.traceStack "fail" $ fail $ "first term of the equation is not flexible: " ++ show t1 ++ "---" ++ show t2

changeGoal (Abs a b) goal = Abs a (changeGoal b goal)
changeGoal _ goal = goal

generate :: (MonadPlus m, MonadGen MetaVariableName m)
         => TermType
         -> [Term]
         -> m Term
generate varType availableTerms = do
  let (assumptions, goal) = getAssumptionsAndGoal varType
  let matchingAssumptions = getMatchingTerms goal $ Var <$> assumptions
  let matchingTerms = getMatchingTerms goal availableTerms
  traceM $ "matching var type: " ++ show varType
  -- Debug.Trace.traceM $ "matching var type: " ++ show varType
  -- Debug.Trace.traceM $ "available terms: " ++ show availableTerms
  traceM $ "Matching assumptions: " ++ show matchingAssumptions
  traceM $ "Matching terms: " ++ show matchingTerms
  traceM ("generate: " ++ show matchingAssumptions)
  head <- anyOf $ matchingAssumptions ++ matchingTerms -- ++ [newMeta]
  traceM $ "generate head: " ++ show head ++ " --- " ++ show matchingAssumptions ++ " --- " ++ show matchingTerms
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
generateLongBody variables head = foldM newArgVar head $ getTermType . Var <$> trace ("assumptions: " ++ show assumptions) assumptions
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

    liftType tType = Data.Foldable.foldr Abs tType $ getTermType . Var <$> variables

    shiftType (Abs _ b) = b
    shiftType t         = t

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
getGoal (Abs _ b) = getGoal b
getGoal g                 = g

foldr :: (TermType -> b -> b) -> b -> TermType -> b
foldr fun initValue (Abs a b) = fun a $ Hou.HigherOrderUnification.foldr fun initValue b
foldr fun initValue v = fun v initValue

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
  -- Abs termType a -> Abs (substitute new index termType) (substitute (raise 1 new) (index+1) a)
  _ -> term

substituteFV :: Term -> FreeVariable -> Term -> Term
substituteFV new fv@(ix, fvType) term | fvType == getTermType new = case term of
  FreeVar (ix2, fvType2) | fvType2 == fvType, ix == ix2 -> new
  App a b termType -> App (substituteFV new fv a) (substituteFV new fv b) (substituteFV new fv termType)
  Abs termType a -> Abs (substituteFV new fv termType) (substituteFV (raise 1 new) fv a)
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
toLongNormalForm t = let result = normalize . toLongNormalForm' . normalize $ t in
  trace ("toLongNormalForm result: arg " ++ show t ++ " --- " ++ show result ++ "types:" ++ show (getTermType t == getTermType result))
  result

toLongNormalForm' :: Term -> Term
toLongNormalForm' (Abs tType body) = Abs tType $ toLongNormalForm' body
toLongNormalForm' (App t1 t2 termType) = App (toLongNormalForm' t1) (toLongNormalForm' t2) termType
toLongNormalForm' v = do
  let (assumptions, _) = getAssumptionsAndGoal . getTermType $ v
  let newVar = case v of
        (Var (ix, termType)) -> Var (ix + length assumptions, termType)
        _                    -> v
  let body =
        Data.Foldable.foldl
          (\b a -> let (Abs _ tType) = getTermType b in App b (toLongNormalForm' a) tType)
          newVar
          (Var <$> assumptions)
  Data.Foldable.foldr (\a b -> Abs (getTermType a) b) body $ Var <$> assumptions

normalize :: Term -> Term
normalize t = case t of
  App l r tType -> case normalize l of
    Abs _ body -> normalize (substitute (normalize r) 0 body)
    l'         -> App l' (normalize r) $ normalize tType
  Abs varType body -> Abs (normalize varType) (normalize body)
  v -> v

getHead :: Term -> (Term, [Term])
getHead t = get t []
  where get (App a b _) ctx = get a (b : ctx)
        get tt          ctx = (tt, ctx)

getHeadConstant :: Term -> Maybe Constant
getHeadConstant t = case t of
  (Constant constant) -> Just constant
  (App m _ _)         -> getHeadConstant m
  _                   -> Nothing

getHeadFreeVar :: Term -> Maybe Variable
getHeadFreeVar t = case t of
  (FreeVar var) -> Just var
  (App m _ _)   -> getHeadFreeVar m
  _             -> Nothing

getHeadMetaVar :: Term -> Maybe MetaVariable
getHeadMetaVar t = case t of
  (MetaVar var) -> Just var
  (App m _ _)   -> getHeadMetaVar m
  _             -> Nothing

-- FIXME: use type from target not from metavariable
getTermType :: Term -> TermType
getTermType (MetaVar (_, t))  = t
getTermType (Constant (_, t)) = t
getTermType (Var (_, t))      = t
getTermType (FreeVar (_, t))  = t
getTermType (App _ _ t)       = t
getTermType (Abs t body)      = Abs t $ getTermType body -- Pi t $ getTermType body
getTermType Uni               = Uni

isLongNormalForm :: Term -> Bool
isLongNormalForm t = case getTermType t of
  (Abs t1 t2) -> case t of
    (Abs _ t3) -> isLongNormalForm t3
    _          -> False
  _ | isVarType t -> do
    let (head, apps) = getHead t
    case head of
      (Abs _ _) -> False
      _         -> and $ isLongNormalForm <$> apps
