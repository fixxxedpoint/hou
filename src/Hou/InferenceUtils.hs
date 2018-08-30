{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleInstances      #-}


{-|
Module      : Hou.InferenceUtils
Description : Utility data types and functions used during the type inference process.
Copyright   : (c) 2018 Łukasz Lachowski <l.lachowski@gmail.com>
License     : MIT, see the file LICENSE
-}
module Hou.InferenceUtils where

import qualified Hou.HigherOrderUnification as H

import           Data.Map


type Name = String

{-|
Class representing a set of typings of variables used by process of type inference/checking.
-}
class Context c n t | c -> n t where
  lookup :: c -> n -> Maybe t
  add :: c -> n -> t -> c

newtype MapContext n t = MC (Map n t)

createMapContext :: MapContext n t
createMapContext = MC Data.Map.empty

instance (Ord n) => Context (MapContext n t) n t where
  lookup (MC c) = flip Data.Map.lookup c
  add (MC c) name term = MC $ Data.Map.insert name term c

implication :: H.Term -> H.Term -> H.Term
implication t1 t2 | H.getTermType t1 == H.starType && H.getTermType t2 == H.starType =
  H.App
  (H.App (H.Constant ("->", H.Pi H.starType (H.Pi H.starType H.starType))) t1 (H.Pi H.starType H.starType))
  t2 H.starType
