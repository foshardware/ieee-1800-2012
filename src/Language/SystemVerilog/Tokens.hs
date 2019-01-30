{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module Language.SystemVerilog.Tokens where

import Control.Lens
import Data.Text (Text)

data Lexer a = L Pos a
  deriving (Show, Eq)

type Pos = (Int, Int)

data Token
    -- Keywords
    = Tok_Accepton
    | Tok_Alias
    | Tok_Always
    | Tok_Alwayscomb
    | Tok_Alwaysff
    | Tok_Alwayslatch
    | Tok_And
    | Tok_Assert
    | Tok_Assign
    | Tok_Assume
    | Tok_Automatic
    | Tok_Before
    | Tok_Begin
    | Tok_Bind
    | Tok_Bins
    | Tok_Binsof
    | Tok_Bit
    | Tok_Break
    | Tok_Buf
    | Tok_Bufif0
    | Tok_Bufif1
    | Tok_Byte
    | Tok_Case
    | Tok_Casex
    | Tok_Casez
    | Tok_Cell
    | Tok_Chandle
    | Tok_Checker
    | Tok_Class
    | Tok_Clocking
    | Tok_Cmos
    | Tok_Config
    | Tok_Const
    | Tok_Constraint
    | Tok_Context
    | Tok_Continue
    | Tok_Cover
    | Tok_Covergroup
    | Tok_Coverpoint
    | Tok_Cross
    | Tok_Deassign
    | Tok_Default
    | Tok_Defparam
    | Tok_Design
    | Tok_Disable
    | Tok_Dist
    | Tok_Do
    | Tok_Edge
    | Tok_Else
    | Tok_End
    | Tok_Endcase
    | Tok_Endchecker
    | Tok_Endclass
    | Tok_Endclocking
    | Tok_Endconfig
    | Tok_Endfunction
    | Tok_Endgenerate
    | Tok_Endgroup
    | Tok_Endinterface
    | Tok_Endmodule
    | Tok_Endpackage
    | Tok_Endprimitive
    | Tok_Endprogram
    | Tok_Endproperty
    | Tok_Endspecify
    | Tok_Endsequence
    | Tok_Endtable
    | Tok_Endtask
    | Tok_Enum
    | Tok_Event
    | Tok_Eventually
    | Tok_Expect
    | Tok_Export
    | Tok_Extends
    | Tok_Extern
    | Tok_Final
    | Tok_Firstmatch
    | Tok_For
    | Tok_Force
    | Tok_Foreach
    | Tok_Forever
    | Tok_Fork
    | Tok_Forkjoin
    | Tok_Function
    | Tok_Generate
    | Tok_Genvar
    | Tok_Global
    | Tok_Highz0
    | Tok_Highz1
    | Tok_If
    | Tok_Iff
    | Tok_Ifnone
    | Tok_Ignorebins
    | Tok_Illegalbins
    | Tok_Implements
    | Tok_Implies
    | Tok_Import
    | Tok_Incdir
    | Tok_Include
    | Tok_Initial
    | Tok_Inout
    | Tok_Input
    | Tok_Inside
    | Tok_Instance
    | Tok_Int
    | Tok_Integer
    | Tok_Interconnect
    | Tok_Interface
    | Tok_Intersect
    | Tok_Join
    | Tok_Joinany
    | Tok_Joinnone
    | Tok_Large
    | Tok_Let
    | Tok_Liblist
    | Tok_Library
    | Tok_Local
    | Tok_Localparam
    | Tok_Logic
    | Tok_Longint
    | Tok_Macromodule
    | Tok_Matches
    | Tok_Medium
    | Tok_Modport
    | Tok_Module
    | Tok_Nand
    | Tok_Negedge
    | Tok_Nettype
    | Tok_New
    | Tok_Nexttime
    | Tok_Nmos
    | Tok_Nor
    | Tok_Noshowcancelled
    | Tok_Not
    | Tok_Notif0
    | Tok_Notif1
    | Tok_Null
    | Tok_Or
    | Tok_Output
    | Tok_Package
    | Tok_Packed
    | Tok_Parameter
    | Tok_Pmos
    | Tok_Posedge
    | Tok_Primitive
    | Tok_Priority
    | Tok_Program
    | Tok_Property
    | Tok_Protected
    | Tok_Pull0
    | Tok_Pull1
    | Tok_Pulldown
    | Tok_Pullup
    | Tok_Pulsestyleondetect
    | Tok_Pulsestyleonevent
    | Tok_Pure
    | Tok_Rand
    | Tok_Randc
    | Tok_Randcase
    | Tok_Randsequence
    | Tok_Rcmos
    | Tok_Real
    | Tok_Realtime
    | Tok_Ref
    | Tok_Reg
    | Tok_Rejecton
    | Tok_Release
    | Tok_Repeat
    | Tok_Restrict
    | Tok_Return
    | Tok_Rnmos
    | Tok_Rpmos
    | Tok_Rtran
    | Tok_Rtranif0
    | Tok_Rtranif1
    | Tok_Salways
    | Tok_Seventually
    | Tok_Snexttime
    | Tok_Suntil
    | Tok_Suntilwith
    | Tok_Scalared
    | Tok_Sequence
    | Tok_Shortint
    | Tok_Shortreal
    | Tok_Showcancelled
    | Tok_Signed
    | Tok_Small
    | Tok_Soft
    | Tok_Solve
    | Tok_Specify
    | Tok_Specparam
    | Tok_Static
    | Tok_String
    | Tok_Strong
    | Tok_Strong0
    | Tok_Strong1
    | Tok_Struct
    | Tok_Super
    | Tok_Supply0
    | Tok_Supply1
    | Tok_Syncaccepton
    | Tok_Syncrejecton
    | Tok_Table
    | Tok_Tagged
    | Tok_Task
    | Tok_This
    | Tok_Throughout
    | Tok_Time
    | Tok_Timeprecision
    | Tok_Timeunit
    | Tok_Tran
    | Tok_Tranif0
    | Tok_Tranif1
    | Tok_Tri
    | Tok_Tri0
    | Tok_Tri1
    | Tok_Triand
    | Tok_Trior
    | Tok_Trireg
    | Tok_Type
    | Tok_Typedef
    | Tok_Union
    | Tok_Unique
    | Tok_Unique0
    | Tok_Unique1
    | Tok_Unsigned
    | Tok_Until
    | Tok_Untilwith
    | Tok_Untyped
    | Tok_Use
    | Tok_Uwire
    | Tok_Var
    | Tok_Vectored
    | Tok_Virtual
    | Tok_Void
    | Tok_Wait
    | Tok_Waitorder
    | Tok_Wand
    | Tok_Weak
    | Tok_Weak0
    | Tok_Weak1
    | Tok_While
    | Tok_Wildcard
    | Tok_Wire
    | Tok_With
    | Tok_Within
    | Tok_Wor
    | Tok_Xnor
    | Tok_Xor

    | Tok_1step
    | Tok_Sample
    | Tok_Option
    | Tok_Typeoption
    | Tok_Std
    | Tok_Randomize

    -- Punctuators
    | Tok_Lparen
    | Tok_Rparen
    | Tok_Lbracket
    | Tok_Rbracket
    | Tok_Lbrace
    | Tok_Rbrace
    | Tok_Colon
    | Tok_Semi
    | Tok_Comma
    | Tok_Dot
    | Tok_Apos

    -- Operators
    | Tok_Plus
    | Tok_Minus
    | Tok_Dollar
    | Tok_Star
    | Tok_Slash
    | Tok_Percent
    | Tok_Amp
    | Tok_Tripleamp
    | Tok_Pipe
    | Tok_Caret
    | Tok_Tilde
    | Tok_Assignop
    | Tok_At
    | Tok_Hash
    | Tok_Question
    | Tok_Coalesce
    | Tok_Namequal
    | Tok_Doublestar
    | Tok_Doubleat
    | Tok_Doublehash
    | Tok_Increment
    | Tok_Decrement
    | Tok_Implicationoverlapped
    | Tok_Implication
    | Tok_Followedbyoverlapped
    | Tok_Followedby
    | Tok_Arrow
    | Tok_Doublearrow
    | Tok_Eqarrow
    | Tok_Eq
    | Tok_Noteq
    | Tok_Lt
    | Tok_Lteq
    | Tok_Gt
    | Tok_Gteq
    | Tok_Ltlt
    | Tok_Gtgt
    | Tok_Notop
    | Tok_Andop
    | Tok_Orop
    | Tok_Shiftl
    | Tok_Shiftr
    | Tok_Assplus
    | Tok_Assminus
    | Tok_Assstar
    | Tok_Assslash
    | Tok_Asspercent
    | Tok_Assamp
    | Tok_Asspipe
    | Tok_Asscaret
    | Tok_Assshiftl
    | Tok_Assshiftr
    | Tok_Assshiftll
    | Tok_Assshiftrr
    | Tok_Equivalent
    | Tok_Notequivalent
    | Tok_Dweq
    | Tok_Dwne

    -- Identifiers
    | Tok_Ident { _parsed :: Text }
    | Tok_TaskFunction  { _parsed :: Text }

    | Tok_Tfsetup
    | Tok_Tfsetuphold
    | Tok_Tfhold
    | Tok_Tfrecovery
    | Tok_Tfremoval
    | Tok_Tfrecrem
    | Tok_Tfskew
    | Tok_Tftimeskew
    | Tok_Tffullskew
    | Tok_Tfperiod
    | Tok_Tfnochange

    -- Literals
    | Tok_StringLit  { _parsed :: Text }

    | Tok_UnsignedNumber  { _parsed :: Text }
    | Tok_BinaryValue  { _parsed :: Text }
    | Tok_OctalValue  { _parsed :: Text }
    | Tok_HexValue  { _parsed :: Text }
    
    | Tok_DecimalBase  { _parsed :: Text }
    | Tok_BinaryBase  { _parsed :: Text }
    | Tok_OctalBase  { _parsed :: Text }
    | Tok_HexBase  { _parsed :: Text }
    
    | Tok_Exp

    | Tok_XDigit  { _parsed :: Text }
    | Tok_ZDigit  { _parsed :: Text }

    -- Other symbols
    | Tok_Unitscope
    | Tok_Rootscope
    | Tok_Pathpulse

  deriving (Eq, Show)

makeFieldsNoPrefix ''Token
