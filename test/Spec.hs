{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Exception (evaluate)

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
  [ testCase "ansi_header.v" $ parse $ ast $ lexer [] $ decodeUtf8 $(embedFile "sample/ansi_header.v")
  ]

parse :: Show a => a -> IO ()
parse s = () <$ evaluate s
