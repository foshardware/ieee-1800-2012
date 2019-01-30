{-# LANGUAGE TemplateHaskell #-}

module Main where

import Data.FileEmbed
import Data.Text.Encoding

import Test.Tasty
import Test.Tasty.HUnit

import Language.SystemVerilog.Lexer
import Language.SystemVerilog.Parser


main :: IO ()
main = defaultMain $ testGroup "IEEE-1800-2012"
  [ ansi_header
  ]

ansi_header :: TestTree
ansi_header = testGroup "ANSI Headers"
  [ testCase "check" $ parse $ ast $ lexer [] $ decodeUtf8 $(embedFile "sample/ansi_header.v")
  ]

parse :: Show a => a -> IO ()
parse _ = pure ()
