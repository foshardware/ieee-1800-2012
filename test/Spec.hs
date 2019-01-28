
module Main where

import Language.SystemVerilog.Alternative
import Language.SystemVerilog.Alternative.Grammar


main :: IO ()
main = putStrLn $ bnfRules ast
