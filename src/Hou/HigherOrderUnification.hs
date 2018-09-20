{-# LANGUAGE FlexibleContexts #-}

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
  termType,
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
  raise,
  isClosed
  )
  where

import qualified Hou.Levels as L
import           Hou.Trace
import qualified Debug.Trace

import qualified Control.Applicative as Appl
import           Control.Arrow
import           Control.Monad
import           Control.Monad.Cont
import           Control.Monad.Gen
import qualified Data.FMList         as FML
import           Data.Foldable
import           Data.List
import           Data.Maybe


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

termType :: TermType
termType = Uni

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
  merge :: s -> s -> s
  emptySolution :: s
  clearSolution :: s -> s
  clearSolution = const emptySolution
  apply :: s -> Term -> Term

newtype ListSolution = LS [(MetaVariable, Term)] deriving (Show)

createListSolution :: ListSolution
createListSolution = LS []

instance Solution ListSolution where
  add (LS l) mv t = LS $ (mv, t) : l
  merge (LS l1) l2 = Data.Foldable.foldr (\val sol -> uncurry (add sol) val) l2 l1
                     -- foldl (\l s -> uncurry (add l) s) l2 $ reverse l1

  emptySolution = createListSolution

  apply (LS []) t = trace "1" t
  apply s (App t1 t2 appType) = trace "2" $ App (apply s t1) (apply s t2) (apply s appType)
  apply s (Abs absType term) = trace "3" $ Abs (apply s absType) (apply s term)
  apply s (Constant (name, cType))  = Constant (name, apply s cType)
  apply s (Var (name, vType)) = Var (name, apply s vType)
  apply s (FreeVar (name, fType)) = FreeVar (name, apply s fType)
  apply s Uni = Uni
  apply s@(LS [(mv1@(mv1Name, _), term)]) t@(MetaVar mv2@(mv2Name, tType)) | mv1Name == mv2Name = trace "5.1" term
                                                                           | otherwise = trace "5.2" t
  apply (LS (s:rest)) t = trace "6" $ apply (LS [s]) $ apply (LS rest) t

{-|
Preunification algorithm tries to solve a given list of equations, returning a solution when all of
the remaining equations are of the flex-flex form. It returns a list of possible solutions.
-}
preunifyAllSolutions :: (Solution s) => [Equation] -> s -> [s]
preunifyAllSolutions eqs s = FML.toList $ preunifyAllSolutions' eqs s

preunifyAllSolutions' :: (Solution s) => [Equation] -> s -> FML.FMList s
preunifyAllSolutions' eqs s = L.iterDepthDefault $ preunifyNonDeterministic eqs s

{-|
Preunification algorithm tries to solve a given list of equations, returning a solution when all of
the remaining equations are of the flex-flex form. It returns a non-deterministic computation
producing a list of possible solutions.
-}
preunifyNonDeterministic :: (Solution s, L.NonDet n) => [Equation] -> s -> L.NonDeterministicT r n s
preunifyNonDeterministic eqs s =
  let nextEnum = toEnum . (1 +) . getMaxMetaFreeVar $ eqs in
  trace "preunifyNonD..." $ runGenTFrom nextEnum $ preunify eqs s

preunify :: (Solution s, L.NonDet n)
         => [Equation]
         -> s
         -> GenT MetaVariableName (L.NonDeterministicT r n) s
preunify eqs s = do
  eqs' <- sequence $ (\(a, b) -> (,) <$> a <*> b) . (toLongNormalForm *** toLongNormalForm) <$> eqs
  preunify' eqs' s

preunify' :: (Solution s, L.NonDet n)
          => [Equation]
          -> s
          -> GenT MetaVariableName (L.NonDeterministicT r n) s
preunify' [] solution = trace "preunify []" $ return solution
preunify' equations solution = L.interrupt $ callCC $ \exit -> do
  -- Debug.Trace.traceM $ "preunify': " ++ show equations
  normalized <- sequence $ (\(a, b) -> (,) <$> a <*> b) . (normalize *** normalize) <$> equations
  -- Debug.Trace.traceM $ "are closed: " ++ show (and $ isClosed <$> [eq | (a, b) <- normalized, eq <- [a, b]])
  simplified <- fixPointOfSimplify normalized
  -- Debug.Trace.traceM $ "preunify' simplified: " ++ show simplified
  when (isSolved simplified) $ exit solution
  -- flexRigid <- L.anyOf . filter (\(a, b) -> isFlexible a && isRigid b) $ simplified
  -- Debug.Trace.traceM $ show simplified
  let flexRigid = head . filter (\(a, b) -> isFlexible a && isRigid b) $ simplified
  -- Debug.Trace.traceM $ "preunify' flexRigid: " ++ show flexRigid
  (mv, term) <- generateStep flexRigid
  let (newSolution, newEquations) = update mv term solution simplified
  -- Debug.Trace.traceM $ "preunify' newEquations: " ++ show newEquations
  -- guard (newEquations /= equations)
  preunify' newEquations newSolution

{-|
Completely unifies a list of equations. It returns a list of possible solutions.
-}
unifyAllSolutions :: (Solution s, L.NonDet m, L.Computation m, MonadPlus m)
                  => [Equation]
                  -> s
                  -> m s
unifyAllSolutions eqs s = L.iterDepthDefault $ unifyNonDeterministic eqs s

{-|
Completely unifies a list of equations. It returns a non-deterministic computation producing a list
of possible solutions.
-}
unifyNonDeterministic :: (Solution s, L.NonDet n)
                      => [Equation]
                      -> s
                      -> L.NonDeterministicT r n s
unifyNonDeterministic eqs s =
  let nextEnum = toEnum . (1 +) . getMaxMetaFreeVar $ eqs in
  trace ("preunifyF..." ++ show eqs) $ runGenTFrom nextEnum $ unify eqs s

unify :: (Solution s, L.NonDet n)
      => [Equation]
      -> s
      -> GenT MetaVariableName (L.NonDeterministicT r n) s
unify eqs s = do
  lnf <- sequence $ (\(a, b) -> (,) <$> a <*> b) . (toLongNormalForm *** toLongNormalForm) <$> eqs
  presolution <- preunify lnf s
  -- Debug.Trace.traceM $ "already preunified: " ++ show presolution
  result <- unify' ((apply presolution *** apply presolution) <$> lnf) presolution
  -- Debug.Trace.traceM "finished"
  return result


unify' :: (Solution s, L.NonDet n)
       => [Equation]
       -> s
       -> GenT MetaVariableName (L.NonDeterministicT r n) s
unify' equations solution = L.interrupt $ callCC $ \exit -> do
  normalized <- sequence $ (\(a, b) -> (,) <$> a <*> b) . (normalize *** normalize) <$> equations
  simplified <- fixPointOfSimplify normalized
  -- Debug.Trace.traceM $ "unify' equations: " ++ show simplified
  -- Debug.Trace.traceM ("unify' 3: " ++ show (isSolved simplified))
  when (null simplified) $ exit solution
  (mv, term) <- generateStep =<< L.anyOf simplified
  -- (mv, term) <- generateStep $ head simplified
  -- Debug.Trace.traceM $ "unify' generateStep: " ++ show (mv, term)
  let (newSolution, newEquations) = update mv term solution simplified
  -- guard (newEquations /= equations)
  unify' newEquations newSolution

update :: (Solution s) => MetaVariable -> Term -> s -> [Equation] -> (s, [Equation])
update mv term solution eqs = do
  let thisSolution = add emptySolution mv term
  let newEquations = (apply thisSolution *** apply thisSolution) <$> eqs
  let newSolution = merge thisSolution solution
  -- let newSolution = add solution mv term
  -- FIXME: verify this
  (newSolution, (getTermType (MetaVar mv), getTermType term) : newEquations)
  -- (newSolution, newEquations)

getMaxMetaFreeVar :: [Equation] -> MetaVariableName
getMaxMetaFreeVar eqs =
  maximum . (:) 0 $ concatMap getMetaFreeVars [z | (x, y) <- eqs, z <- [x, y]]

getMetavarId :: MetaVariable -> MetaVariableName
getMetavarId (ix, _) = ix

getMetaFreeVars :: Term -> [MetaVariableName]
getMetaFreeVars t = getMetaFreeVars' t []
getMetaFreeVars' :: Term -> [MetaVariableName] -> [MetaVariableName]
getMetaFreeVars' t r = case t of
  (MetaVar (metaVar, mvType)) -> getMetaFreeVars' mvType $ metaVar : r
  (Constant (_, consType))    -> getMetaFreeVars' consType r
  (Var (_, varType))          -> getMetaFreeVars' varType r
  (FreeVar (freeVar, fvType)) -> getMetaFreeVars' fvType $ freeVar : r
  (App a b appType)           -> getMetaFreeVars' appType $ getMetaFreeVars' b $ getMetaFreeVars' a r
  (Abs absType body)          -> getMetaFreeVars' absType $ getMetaFreeVars' body r
  _                           -> r

sameName :: Term -> Term -> Bool
sameName (FreeVar (name1, _)) (FreeVar (name2, _)) | name1 == name2 = True
sameName (Constant (name1, _)) (Constant (name2, _)) | name1 == name2 = True
sameName _ _ = False

simplify :: (L.NonDet m, MonadPlus m, MonadGen MetaVariableName m) => Equation -> m [Equation]
simplify (t1, t2)
  | t1 == t2 = do
      -- Debug.Trace.traceM "I am here 0"
      return [] -- check for metavars?
  -- | not (isClosed t1 && isClosed t2) = return []
  -- TODO | try to avoid this cuz it is also changing free variables in types
  | (Abs type1 a) <- t1,
    (Abs type2 b) <- t2,
    type1 == type2 = do
      newVar <- gen
      let newCons = FreeVar (newVar, type1)
      let newA = substitute newCons 0 a
      let newB = substitute newCons 0 b
      -- Debug.Trace.traceM $ "I am here 2" ++ show type1 ++ "---" ++ show type2
      -- (:) (type1, type2) <$> simplify (newA, newB)
      simplify (newA, newB)
  | (c1, ctx1) <- getHead t1,
    (c2, ctx2) <- getHead t2,
    isFreeVarOrConstant c1 && isFreeVarOrConstant c2 = do
    -- c1 == c2 = do
    -- c1 == c2 = do
      -- Debug.Trace.traceM $ "I am here 4" ++ show c1 ++ "---" ++ show c2
      -- guard (c1 == c2) -- this can fail the whole process
      guard (sameName c1 c2) -- this can fail the whole process
      -- Debug.Trace.traceM "I am here 5"
      (:) (getTermType c1, getTermType c2) <$> fold <$> mapM simplify (zip ctx1 ctx2) -- faster than using fixPointOfSimplify
  | isRigid t1 && isFlexible t2 = trace "rigid-flex" $ return [(t2, t1)]
  | isFlexible t1 && isRigid t2 = trace ("flex-rigid: " ++ show t1 ++ " --- " ++ show t2) $ return [(t1, t2)]
  | isFlexible t1 && isFlexible t2 = trace "flex-flex" $ return [(t1, t2)]
  | otherwise = Debug.Trace.trace ("otherwise: " ++ show t1 ++ "---" ++ show t2) L.failure
  -- | otherwise = trace ("otherwise: " ++ show t1 ++ "---" ++ show t2) $ return [(t1, t2)]
  -- | otherwise = fail "otherwise"

fixPointOfSimplify :: (L.NonDet m, MonadPlus m, MonadGen MetaVariableName m) => [Equation] -> m [Equation]
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
isFlexible t | (MetaVar _, _) <- getHead t = Debug.Trace.trace "is flexible" True
             | otherwise = trace ("is not flexible" ++ show t) False

isVarType :: TermType -> Bool
isVarType (Abs _ _) = False
isVarType _         = True

{-|
Tries to non-deterministically solve an equation using projection or imitation.
-}
generateStep :: (MonadPlus m, MonadGen MetaVariableName m, L.NonDet m)
             => Equation
             -> m (MetaVariable, Term)
generateStep (flex, rigid) | isFlexible flex = do
  let (flexTerm, _) = getHead flex
  flexVariable <- case flexTerm of
                   (MetaVar var) -> return var
                   _             -> L.failure
  let headConstant = getHeadConstant rigid
  let headFreeVar  = getHeadFreeVar rigid
  let headMetaVar  = getHeadMetaVar rigid
  let availableTerms = (Constant <$> maybeToList headConstant) ++
                       (filter (/= flexTerm) $ MetaVar <$> maybeToList headMetaVar) ++
                       (FreeVar <$> maybeToList headFreeVar)
  traceM $ "before generate: " ++ show headConstant
  traceM $ "before generate head FreeVar: " ++ show headFreeVar
  traceM $ "before generate available terms: " ++ show availableTerms
  -- Debug.Trace.traceM $ "generateStep rigid: " ++ show rigid
  -- Debug.Trace.traceM  $ "generateStep flex: " ++ show flex
  generatedTerm <- generate (getTermType flexTerm) availableTerms
  -- Debug.Trace.traceM $ "generated term: " ++ show flexVariable ++ "---" ++ show generatedTerm
  return (flexVariable, generatedTerm)
generateStep (t1, t2) = fail $ "first term of the equation is not flexible: " ++ show t1 ++ "---" ++ show t2

changeGoal (Abs a b) goal = Abs a (changeGoal b goal)
changeGoal _ goal = goal

generate :: (MonadPlus m, MonadGen MetaVariableName m, L.NonDet m)
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
  traceM $ "is empty :" ++ show (null (matchingTerms ++ matchingAssumptions))
  head <- L.anyOf $ matchingAssumptions ++ matchingTerms
  -- head <- L.anyOf $ matchingTerms ++ matchingAssumptions
  traceM $ "generate head: " ++ show head ++ " --- " ++ show matchingAssumptions ++ " --- " ++ show matchingTerms
  result <- generateLongTerm assumptions head
  traceM ("generate result: " ++ show result)
  toLongNormalForm result

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
getMatchingTerms goal terms = good ++ bad
  where (good, bad) = partition ((goal ==) . getGoal . getTermType) terms

getGoal :: TermType -> TermType
getGoal (Abs _ b) = getGoal b
getGoal g                 = g

foldr :: (TermType -> b -> b) -> b -> TermType -> b
foldr fun initValue (Abs a b) = fun a $ Hou.HigherOrderUnification.foldr fun initValue b
foldr fun initValue v = fun v initValue

isSolved :: [Equation] -> Bool
isSolved [] = True
isSolved equations = trace ("isSolved: " ++ show equations) $
  and $ uncurry (&&) . (isFlexible *** isFlexible) <$> equations

substitute :: Term -> DeBruijnIndex -> Term -> Term
-- substitute new index term = case term of
--   (Var (deBruijnIndex, varType)) -> case compare deBruijnIndex index of
--     LT -> Var (deBruijnIndex, varType)
--     EQ -> new
--     GT -> Var (deBruijnIndex-1, varType)
--   App a b termType -> App (substitute new index a) (substitute new index b) termType
--   Abs termType a -> Abs termType (substitute (raise 1 new) (index+1) a)
--   MetaVar (name, mvType) -> MetaVar (name,  mvType)
--   Constant (name, consType) -> Constant (name, consType)
--   FreeVar (name, fvType) -> FreeVar (name, fvType)
--   _ -> term
substitute new index term = case term of
  (Var (deBruijnIndex, varType)) -> case compare deBruijnIndex index of
    LT -> Var (deBruijnIndex, substitute new index varType)
    EQ -> new
    GT -> Var (deBruijnIndex-1, substitute new index varType)
  App a b termType -> App (substitute new index a) (substitute new index b) (substitute new index termType)
  Abs termType a -> Abs (substitute new index termType) (substitute (raise 1 new) (index+1) a)
  MetaVar (name, mvType) -> MetaVar (name, substitute new index mvType)
  Constant (name, consType) -> Constant (name, substitute new index consType)
  FreeVar (name, fvType) -> FreeVar (name, substitute new index fvType)
  _ -> term

substituteFV :: Term -> FreeVariable -> Term -> Term
substituteFV new fv@(ix, fvType) term | fvType == getTermType new = case term of
  FreeVar (ix2, fvType2) | fvType2 == fvType, ix == ix2 -> new
  App a b termType -> App (substituteFV new fv a) (substituteFV new fv b) (substituteFV new fv termType)
  Abs termType a -> Abs termType (substituteFV (raise 1 new) fv a)
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

normalize :: (L.NonDet m, Monad m) => Term -> m Term
normalize t = case t of
  App l r tType -> do
    normalizedL <- normalize l
    case normalizedL of
      Abs _ body -> L.interrupt $ normalize (substitute r 0 body)
      -- Abs _ body -> L.interrupt $ normalize =<< (\r' -> substitute r' 0 body) <$> normalize r
      -- Abs _ body -> normalize =<< (\r' -> substitute r' 0 body) <$> normalize r
      l'         -> App l' <$> normalize r <*> normalize tType
  Abs varType body -> Abs <$> normalize varType <*> normalize body
  Uni -> return Uni
  -- _ -> return t
  _ -> do
    let vType = getTermType t
    setVarType t <$> (normalize vType)

getHead :: Term -> (Term, [Term])
getHead t = get t []
  where get (App a b _) ctx = get a (b : ctx)
        get (Abs _ body) ctx = get body ctx
        get tt          ctx = (tt, ctx)

getHeadConstant :: Term -> Maybe Constant
getHeadConstant t = case (fst . getHead $ t) of
  Constant constant -> Just constant
  _                   -> Nothing

getHeadFreeVar :: Term -> Maybe Variable
getHeadFreeVar t = case (fst . getHead $ t) of
  FreeVar var -> Just var
  _             -> Nothing

getHeadMetaVar :: Term -> Maybe MetaVariable
getHeadMetaVar t = case (fst . getHead $ t) of
  MetaVar var -> Just var
  _             -> Nothing

getTermType :: Term -> TermType
getTermType (MetaVar (_, t))  = t
getTermType (Constant (_, t)) = t
getTermType (Var (_, t))      = t
getTermType (FreeVar (_, t))  = t
getTermType (App _ _ t)       = t
getTermType (Abs t body)      = Abs t $ getTermType body -- Pi t $ getTermType body
getTermType Uni               = Uni

setVarType :: Term -> TermType -> Term
setVarType t newType = case t of
  MetaVar (name, _) -> MetaVar (name, newType)
  Constant (name, _) -> Constant (name, newType)
  Var (name, _) -> Var (name, newType)
  FreeVar (name, _) -> FreeVar (name, newType)
  _ -> t

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

toLongNormalForm :: (L.NonDet m, Monad m) => Term -> m Term
toLongNormalForm t = do
  result <- normalize . toLongNormalForm' =<< normalize t
  traceM $ "toLongNormalForm result: arg " ++ show t ++ " --- " ++ show result ++ "types:" ++ show (getTermType t == getTermType result)
  return result

toLongNormalForm' :: Term -> Term
toLongNormalForm' (Abs tType body) = Abs (toLongNormalForm' tType) (toLongNormalForm' body)
toLongNormalForm' (App t1 t2 termType) = App (toLongNormalForm' t1) (toLongNormalForm' t2) (toLongNormalForm' termType)
toLongNormalForm' v = do
  let (assumptions, _) = getAssumptionsAndGoal . getTermType $ v
  let newVar = case v of
        (Var (ix, termType)) -> Var (ix + length assumptions, toLongNormalForm' termType)
        _                    -> do
          let vType = getTermType v
          setVarType v $ toLongNormalForm' vType
  let body =
        Data.Foldable.foldl
          (\b a -> let (Abs _ tType) = getTermType b in App b (toLongNormalForm' a) tType)
          newVar
          (Var <$> assumptions)
  Data.Foldable.foldr (\a b -> Abs (getTermType a) b) body $ Var <$> assumptions

isClosed :: Term -> Bool
isClosed = isClosed' 0
isClosed' :: DeBruijnIndex -> Term -> Bool
isClosed' max t = case t of
  MetaVar (_, mvType) -> isClosed' max mvType
  Constant (_, consType) -> isClosed' max consType
  Var (name, varType) -> (name < max) && isClosed' max varType
  FreeVar (_, fvType) -> isClosed' max fvType
  App t1 t2 appType -> isClosed' max t1 && isClosed' max t2 && isClosed' max appType
  Abs absType body -> isClosed' max absType && isClosed' (max+1) body
  Uni -> True

