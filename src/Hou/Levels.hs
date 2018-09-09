{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE UndecidableInstances       #-}

{-|
Module      : Hou.Levels
Description : Provides basic definitions for declaring unbounded backtracking computations.
              Implements two search strategies: deepening depth-first search and breadth-first
              search. It is based on the article "Reinventing Haskell Backtracking" of Sebastian
              Fischer <https://www-ps.informatik.uni-kiel.de/~sebf/data/pub/atps09.pdf>.
Copyright   : (c) 2018 Łukasz Lachowski <l.lachowski@gmail.com>
License     : MIT, see the file LICENSE
-}
module Hou.Levels where

import           Hou.Trace

import           Control.Applicative as Appl
import           Control.Monad.Cont
import           Control.Monad.Gen
import qualified Data.FMList         as FML


class NonDet n where
  failure :: n a
  choice :: n a -> n a -> n a

newtype DiffList a = DiffList { (>>>) :: [a] -> [a] }

newtype Levels n a = Levels { levels :: [n a] }

newtype DepthBounded n a = DepthBounded {
                             (!) :: Integer     -- ^ current depth
                                 -> (n a, Bool) -- ^ result and a bool indicator of whether it
                                                --   reached the bottom of the computation
                           }

newtype NonDeterministicT r (m :: * -> *) a = NDT { (!!>) :: ContT r m a }
  deriving (Functor, Applicative, Monad, MonadCont, MonadTrans)

instance (NonDet n) => NonDet (DepthBounded n) where
  failure = DepthBounded . const $ (failure, True)
  choice a b = DepthBounded $ \d -> if d == 0 then (failure, False)
                                    else do
                                           let (rA, contA) = a ! (d-1)
                                           let (rB, contB) = b ! (d-1)
                                           (choice rA rB, contA && contB)

instance (NonDet m) => MonadPlus (NonDeterministicT r m) where
  mzero = NDT . ContT . const $ failure
  mplus a b = NDT . ContT $ \c -> choice ((runContT . (!!>)) a c) ((runContT . (!!>)) b c)

instance (MonadGen e m) => MonadGen e (NonDeterministicT r m) where
  gen = lift gen

instance (NonDet m) => NonDet (NonDeterministicT r m) where
  failure = mzero
  choice = mplus

instance (NonDet m) => Alternative (NonDeterministicT r m) where
  empty = mzero
  (<|>) = mplus

instance (NonDet n) => NonDet (Levels n) where
  failure = Levels { levels = [] }
  choice a b = Levels { levels = failure : merge (levels a) (levels b) }

merge :: (NonDet n) => [n a] -> [n a] -> [n a]
merge [] ys         = ys
merge xs []         = xs
merge (x:xs) (y:ys) = choice x y : merge xs ys

class Computation c where
  yield :: a -> c a

instance Computation DiffList where
  yield = singleton

instance (Computation n) => Computation (Levels n) where
  yield x = Levels { levels = [yield x] }

instance Computation FML.FMList where
  yield = FML.singleton

instance Monoid (DiffList a) where
  mempty = Appl.empty
  mappend = (<|>)

instance Functor DiffList where
  fmap = liftM

instance Applicative DiffList where
  pure = return
  (<*>) = ap

instance Monad DiffList where
  return = singleton
  m >>= f = mconcat $ f <$> toList m

instance Alternative DiffList where
  empty = Hou.Levels.empty
  (<|>) = (+++)

instance MonadPlus DiffList where
  mzero = Appl.empty
  mplus = (<|>)

instance NonDet DiffList where
  failure = mzero
  choice = mplus

instance NonDet FML.FMList where
  failure = mzero
  choice = mappend

instance (Computation m, Monad m) => Computation (GenT e m) where
  yield = lift . yield

empty :: DiffList a
empty = DiffList { (>>>)=id }

singleton :: a -> DiffList a
singleton x = DiffList { (>>>)=(x:)}

(+++) :: DiffList a -> DiffList a -> DiffList a
a +++ b = DiffList { (>>>)=(a >>>) . (b >>>) }

toList :: DiffList a -> [a]
toList a = a >>> []

runLevels :: (NonDet n) => Levels n a -> n a
runLevels = foldr choice failure . levels

levelSearch :: (Computation m, NonDet m) => NonDeterministicT a (Levels m) a -> m a
levelSearch c = runLevels . (runContT . (!!>)) c $ yield

levelIter :: (Computation m, NonDet m)
          => Integer
          -> NonDeterministicT a (DepthBounded m) a
          -> Levels m a
levelIter step c = do
  let levelValues = [ (runContT . (!!>) $ c) yieldB ! d | d <- [0,step..] ]
  let (notFinished, afterFinished) = span (\(_, finished) -> not finished) levelValues
  Levels {
    levels = fst <$> notFinished ++ take 1 afterFinished
  }
  where yieldB x =
          DepthBounded {
            (!) = \d -> trace ("levelIter: " ++ show d) $
                          if d < step then trace "yielding"  (yield x, True)
                                      else trace "levelIter" (failure, True)
          }

iterDepth :: (Computation m, NonDet m)
          => Integer
          -> NonDeterministicT a (DepthBounded m) a
          -> m a
iterDepth step = runLevels . levelIter step

iterDepthDefault :: (Computation m, NonDet m) => NonDeterministicT a (DepthBounded m) a -> m a
iterDepthDefault = iterDepth 200

interrupt :: (Alternative a) => a b -> a b
interrupt v = v <|> Appl.empty

anyOf :: (Alternative m) => [a] -> m a
anyOf []     = Appl.empty
anyOf (x:xs) = pure x <|> anyOf xs

example :: NonDeterministicT r DiffList Int
example = return 10 <|> return 11 <|> return 100
