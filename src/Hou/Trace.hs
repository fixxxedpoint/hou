{-|
Module      : Hou.Trace
Copyright   : (c) 2018 Łukasz Lachowski <l.lachowski@gmail.com>
License     : MIT, see the file LICENSE
-}
module Hou.Trace where


traceM _ = return ()

trace = flip const
