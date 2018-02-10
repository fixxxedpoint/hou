{-|
Module      : Main
Description : Simple main module trying to parse a lambda term from the standard input and returning
              its type.
Copyright   : (c) 2018 Łukasz Lachowski <l.lachowski@gmail.com>
License     : MIT, see the file LICENSE
-}
module Main where

import           Hou.SystemF


main :: IO ()
main = do
  input <- getContents
  let term = read input
  print $ inferType term
