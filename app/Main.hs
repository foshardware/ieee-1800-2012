
module Main where

import Language.SystemVerilog.Alternative
import Language.SystemVerilog.Alternative.Grammar


main :: IO ()
main = writeFile "Parser.y" $ happyRules ast
