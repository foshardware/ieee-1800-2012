{
module Language.SystemVerilog.Lexer
    ( Lexer (..)
    , Token (..)
    , lexer
    ) where

import Data.Char (ord)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import           Language.SystemVerilog.Tokens
}

$any     = [.\n\r]
@newline = [\n\r] | \r\n
@comment = "/*" $any* "*/"
         | "//" .* @newline

@nul_eof = \0 $any*

@preprocessor = \# .* @newline

$ident_start = [a-zA-Z_]
$ident_part  = [a-zA-Z_0-9]
$const_part  = [A-Z_]

@time_unit = s | ms | us | ns | ps | fs

$x_digit = [xX]
$z_digit = [zZ\?]

$decimal_digit = [0-9]
$binary_digit  = [0-1$x_digit$z_digit]
$octal_digit   = [0-7$x_digit$z_digit]
$hex_digit     = [0-9a-fA-F$x_digit$z_digit]

@decimal_base = \'[sS]?[dD]
@binary_base  = \'[sS]?[bB]
@octal_base   = \'[sS]?[oO]
@hex_base     = \'[sS]?[hH]

$sign = [\+\-]
$exp  = [eE]

@string_character   = [^\"\\]

tokens :-

$white+       ;
@comment      ;
@nul_eof      ;
@preprocessor ;

-- Keywords
accept_on     { constTok Tok_Accepton      }
alias         { constTok Tok_Alias         }
always        { constTok Tok_Always        }
always_comb   { constTok Tok_Alwayscomb    }
always_ff     { constTok Tok_Alwaysff      }
always_latch  { constTok Tok_Alwayslatch   }
and           { constTok Tok_And           }
assert        { constTok Tok_Assert        }
assign        { constTok Tok_Assign        }
assume        { constTok Tok_Assume        }
automatic     { constTok Tok_Automatic     }
before        { constTok Tok_Before        }
begin         { constTok Tok_Begin         }
bind          { constTok Tok_Bind          }
bins          { constTok Tok_Bins          }
binsof        { constTok Tok_Binsof        }
bit           { constTok Tok_Bit           }
break         { constTok Tok_Break         }
buf           { constTok Tok_Buf           }
bufif0        { constTok Tok_Bufif0        }
bufif1        { constTok Tok_Bufif1        }
byte          { constTok Tok_Byte          }
case          { constTok Tok_Case          }
casex         { constTok Tok_Casex         }
casez         { constTok Tok_Casez         }
cell          { constTok Tok_Cell          }
chandle       { constTok Tok_Chandle       }
checker       { constTok Tok_Checker       }
class         { constTok Tok_Class         }
clocking      { constTok Tok_Clocking      }
cmos          { constTok Tok_Cmos          }
config        { constTok Tok_Config        }
const         { constTok Tok_Const         }
constraint    { constTok Tok_Constraint    }
context       { constTok Tok_Context       }
continue      { constTok Tok_Continue      }
cover         { constTok Tok_Cover         }
covergroup    { constTok Tok_Covergroup    }
coverpoint    { constTok Tok_Coverpoint    }
cross         { constTok Tok_Cross         }
deassign      { constTok Tok_Deassign      }
default       { constTok Tok_Default       }
defparam      { constTok Tok_Defparam      }
design        { constTok Tok_Design        }
disable       { constTok Tok_Disable       }
dist          { constTok Tok_Dist          }
do            { constTok Tok_Do            }
edge          { constTok Tok_Edge          }
else          { constTok Tok_Else          }
end           { constTok Tok_End           }
endcase       { constTok Tok_Endcase       }
endchecker    { constTok Tok_Endchecker    }
endclass      { constTok Tok_Endclass      }
endconfig     { constTok Tok_Endconfig     }
endfunction   { constTok Tok_Endfunction   }
endgenerate   { constTok Tok_Endgenerate   }
endgroup      { constTok Tok_Endgroup      }
endinterface  { constTok Tok_Endinterface  }
endmodule     { constTok Tok_Endmodule     }
endpackage    { constTok Tok_Endpackage    }
endprimitive  { constTok Tok_Endprimitive  }
endprogram    { constTok Tok_Endprogram    }
endproperty   { constTok Tok_Endproperty   }
endspecify    { constTok Tok_Endspecify    }
endsequence   { constTok Tok_Endsequence   }
endtable      { constTok Tok_Endtable      }
endtask       { constTok Tok_Endtask       }
enum          { constTok Tok_Enum          }
event         { constTok Tok_Event         }
eventually    { constTok Tok_Eventually    }
expect        { constTok Tok_Expect        }
export        { constTok Tok_Export        }
extends       { constTok Tok_Extends       }
extern        { constTok Tok_Extern        }
final         { constTok Tok_Final         }
first_match   { constTok Tok_Firstmatch    }
for           { constTok Tok_For           }
force         { constTok Tok_Force         }
foreach       { constTok Tok_Foreach       }
forever       { constTok Tok_Forever       }
fork          { constTok Tok_Fork          }
forkjoin      { constTok Tok_Forkjoin      }
function      { constTok Tok_Function      }
generate      { constTok Tok_Generate      }
genvar        { constTok Tok_Genvar        }
global        { constTok Tok_Global        }
highz0        { constTok Tok_Highz0        }
highz1        { constTok Tok_Highz1        }
if            { constTok Tok_If            }
iff           { constTok Tok_Iff           }
ifnone        { constTok Tok_Ifnone        }
ignore_bins   { constTok Tok_Ignorebins    }
illegal_bins  { constTok Tok_Illegalbins   }
implements    { constTok Tok_Implements    }
implies       { constTok Tok_Implies       }
import        { constTok Tok_Import        }
incdir        { constTok Tok_Incdir        }
include       { constTok Tok_Include       }
initial       { constTok Tok_Initial       }
inout         { constTok Tok_Inout         }
input         { constTok Tok_Input         }
inside        { constTok Tok_Inside        }
instance      { constTok Tok_Instance      }
int           { constTok Tok_Int           }
integer       { constTok Tok_Integer       }
interconnect  { constTok Tok_Interconnect  }
interface     { constTok Tok_Interface     }
intersect     { constTok Tok_Intersect     }
join          { constTok Tok_Join          }
join_any      { constTok Tok_Joinany       }
join_none     { constTok Tok_Joinnone      }
large         { constTok Tok_Large         }
let           { constTok Tok_Let           }
liblist       { constTok Tok_Liblist       }
library       { constTok Tok_Library       }
local         { constTok Tok_Local         }
localparam    { constTok Tok_Localparam    }
logic         { constTok Tok_Logic         }
longint       { constTok Tok_Longint       }
macromodule   { constTok Tok_Macromodule   }
matches       { constTok Tok_Matches       }
medium        { constTok Tok_Medium        }
modport       { constTok Tok_Modport       }
module        { constTok Tok_Module        }
nand          { constTok Tok_Nand          }
negedge       { constTok Tok_Negedge       }
nettype       { constTok Tok_Nettype       }
new           { constTok Tok_New           }
nexttime      { constTok Tok_Nexttime      }
nmos          { constTok Tok_Nmos          }
nor           { constTok Tok_Nor           }
noshowcancelled   { constTok Tok_Noshowcancelled }
not           { constTok Tok_Not           }
notif0        { constTok Tok_Notif0        }
notif1        { constTok Tok_Notif1        }
null          { constTok Tok_Null          }
or            { constTok Tok_Or            }
output        { constTok Tok_Output        }
package       { constTok Tok_Package       }
packed        { constTok Tok_Packed        }
parameter     { constTok Tok_Parameter     }
pmos          { constTok Tok_Pmos          }
posedge       { constTok Tok_Posedge       }
primitive     { constTok Tok_Primitive     }
priority      { constTok Tok_Priority      }
program       { constTok Tok_Program       }
property      { constTok Tok_Property      }
protected     { constTok Tok_Protected     }
pull0         { constTok Tok_Pull0         }
pull1         { constTok Tok_Pull1         }
pulldown      { constTok Tok_Pulldown      }
pullup        { constTok Tok_Pullup        }
pulsestyle_ondetect  { constTok Tok_Pulsestyleondetect }
pulsestyle_onevent   { constTok Tok_Pulsestyleonevent  }
pure          { constTok Tok_Pure          }
rand          { constTok Tok_Rand          }
randc         { constTok Tok_Randc         }
randcase      { constTok Tok_Randcase      }
randsequence  { constTok Tok_Randsequence  }
rcmos         { constTok Tok_Rcmos         }
real          { constTok Tok_Real          }
realtime      { constTok Tok_Realtime      }
ref           { constTok Tok_Ref           }
reg           { constTok Tok_Reg           }
reject_on     { constTok Tok_Rejecton      }
release       { constTok Tok_Release       }
repeat        { constTok Tok_Repeat        }
restrict      { constTok Tok_Restrict      }
return        { constTok Tok_Return        }
rnmos         { constTok Tok_Rnmos         }
rpmos         { constTok Tok_Rpmos         }
rtran         { constTok Tok_Rtran         }
rtranif0      { constTok Tok_Rtranif0      }
rtranif1      { constTok Tok_Rtranif1      }
s_always      { constTok Tok_Salways       }
s_eventually  { constTok Tok_Seventually   }
s_nexttime    { constTok Tok_Snexttime     }
s_until       { constTok Tok_Suntil        }
s_until_with  { constTok Tok_Suntilwith    }
scalared      { constTok Tok_Scalared      }
sequence      { constTok Tok_Sequence      }
shortint      { constTok Tok_Shortint      }
shortreal     { constTok Tok_Shortreal     }
showcancelled { constTok Tok_Showcancelled }
signed        { constTok Tok_Signed        }
small         { constTok Tok_Small         }
soft          { constTok Tok_Soft          }
solve         { constTok Tok_Solve         }
specify       { constTok Tok_Specify       }
specparam     { constTok Tok_Specparam     }
static        { constTok Tok_Static        }
string        { constTok Tok_String        }
strong        { constTok Tok_Strong        }
strong0       { constTok Tok_Strong0       }
strong1       { constTok Tok_Strong1       }
struct        { constTok Tok_Struct        }
super         { constTok Tok_Super         }
supply0       { constTok Tok_Supply0       }
supply1       { constTok Tok_Supply1       }
sync_accept_on   { constTok Tok_Syncaccepton  }
sync_reject_on   { constTok Tok_Syncaccepton  }
table         { constTok Tok_Table         }
tagged        { constTok Tok_Tagged        }
task          { constTok Tok_Task          }
this          { constTok Tok_This          }
throughout    { constTok Tok_Throughout    }
time          { constTok Tok_Time          }
timeprecision { constTok Tok_Timeprecision }
timeunit      { constTok Tok_Timeunit      }
tran          { constTok Tok_Tran          }
tranif0       { constTok Tok_Tranif0       }
tranif1       { constTok Tok_Tranif1       }
tri           { constTok Tok_Tri           }
tri0          { constTok Tok_Tri0          }
tri1          { constTok Tok_Tri1          }
triand        { constTok Tok_Triand        }
trior         { constTok Tok_Trior         }
trireg        { constTok Tok_Trireg        }
type          { constTok Tok_Type          }
typedef       { constTok Tok_Typedef       }
union         { constTok Tok_Union         }
unique        { constTok Tok_Unique        }
unique0       { constTok Tok_Unique0       }
unsigned      { constTok Tok_Unsigned      }
until         { constTok Tok_Until         }
until_with    { constTok Tok_Untilwith     }
untyped       { constTok Tok_Untyped       }
use           { constTok Tok_Use           }
uwire         { constTok Tok_Uwire         }
var           { constTok Tok_Var           }
vectored      { constTok Tok_Vectored      }
void          { constTok Tok_Void          }
virtual       { constTok Tok_Virtual       }
wait          { constTok Tok_Wait          }
wait_order    { constTok Tok_Waitorder     }
wand          { constTok Tok_Wand          }
weak          { constTok Tok_Weak          }
weak0         { constTok Tok_Weak0         }
weak1         { constTok Tok_Weak1         }
while         { constTok Tok_While         }
wildcard      { constTok Tok_Wildcard      }
wire          { constTok Tok_Wire          }
with          { constTok Tok_With          }
within        { constTok Tok_Within        }
wor           { constTok Tok_Wor           }
xnor          { constTok Tok_Xnor          }
xor           { constTok Tok_Xor           }

1step         { constTok Tok_1step         }
sample        { constTok Tok_Sample        }
option        { constTok Tok_Option        }
type_option   { constTok Tok_Typeoption    }
std           { constTok Tok_Std           }
randomize     { constTok Tok_Randomize     }

-- Punctuators
\( { constTok Tok_Lparen   }
\) { constTok Tok_Rparen   }
\[ { constTok Tok_Lbracket }
\] { constTok Tok_Rbracket }
\{ { constTok Tok_Lbrace   }
\} { constTok Tok_Rbrace   }
\: { constTok Tok_Colon    }
\; { constTok Tok_Semi     }
\, { constTok Tok_Comma    }
\. { constTok Tok_Dot      }
\' { constTok Tok_Apos     }

-- Operators
\+     { constTok Tok_Plus       }
\-     { constTok Tok_Minus      }
\$     { constTok Tok_Dollar     }
\*     { constTok Tok_Star       }
\/     { constTok Tok_Slash      }
\%     { constTok Tok_Percent    }
\&     { constTok Tok_Amp        }
\|     { constTok Tok_Pipe       }
\^     { constTok Tok_Caret      }
\!     { constTok Tok_Notop      }
\~     { constTok Tok_Tilde      }
\=     { constTok Tok_Assignop   }
\@     { constTok Tok_At         }
\#     { constTok Tok_Hash       }
\?     { constTok Tok_Question   }
\?\?   { constTok Tok_Coalesce   }
\:\:   { constTok Tok_Namequal   }
\@\@   { constTok Tok_Doubleat   }
\*\*   { constTok Tok_Doublestar }
\#\#   { constTok Tok_Doublehash }
\+\+   { constTok Tok_Increment  }
\-\-   { constTok Tok_Decrement  }
\&\&   { constTok Tok_Andop      }
\|\|   { constTok Tok_Orop       }
\-\>   { constTok Tok_Arrow      }
\=\>   { constTok Tok_Eqarrow    }
\:\=   { constTok Tok_Dweq       }
\:\/   { constTok Tok_Dwne       }
\=\=   { constTok Tok_Eq         }
\!\=   { constTok Tok_Noteq      }
\<     { constTok Tok_Lt         }
\<\=   { constTok Tok_Lteq       }
\>     { constTok Tok_Gt         }
\>\=   { constTok Tok_Gteq       }
\<\<   { constTok Tok_Ltlt       }
\>\>   { constTok Tok_Gtgt       }
\+\=   { constTok Tok_Assplus    }
\-\=   { constTok Tok_Assminus   }
\*\=   { constTok Tok_Assstar    }
\/\=   { constTok Tok_Assslash   }
\%\=   { constTok Tok_Asspercent }
\&\=   { constTok Tok_Assamp     }
\|\=   { constTok Tok_Asspipe    }
\^\=   { constTok Tok_Asscaret   }
\=\=\= { constTok Tok_Equivalent }
\!\=\= { constTok Tok_Notequivalent }
\&\&\& { constTok Tok_Tripleamp   }
\-\>\> { constTok Tok_Doublearrow }
\<\<\= { constTok Tok_Assshiftl   }
\>\>\= { constTok Tok_Assshiftr   }
\|\-\> { constTok Tok_Implicationoverlapped }
\|\=\> { constTok Tok_Implication           }
\#\-\# { constTok Tok_Followedbyoverlapped  }
\#\=\# { constTok Tok_Followedby            }
\<\<\<\= { constTok Tok_Assshiftll  }
\>\>\>\= { constTok Tok_Assshiftrr  }


-- Numeric literals

$x_digit \_*   { textTok Tok_XDigit  }
$z_digit \_*   { textTok Tok_ZDigit  }

$decimal_digit  [\_$decimal_digit]*  { textTok Tok_UnsignedNumber  }
$binary_digit   [\_$binary_digit]*   { textTok Tok_BinaryValue     }
$octal_digit    [\_$octal_digit]*    { textTok Tok_OctalValue      }
$hex_digit      [\_$hex_digit]*      { textTok Tok_HexValue        }

@decimal_base    { textTok Tok_DecimalBase    } 
@binary_base     { textTok Tok_BinaryBase     }
@octal_base      { textTok Tok_OctalBase      }
@hex_base        { textTok Tok_HexBase        }

-- Other symbols
\$root      { constTok Tok_Rootscope }
\$unit      { constTok Tok_Unitscope }
\$pathpulse { constTok Tok_Pathpulse }

\$setup     { constTok Tok_Tfsetup     }
\$setuphold { constTok Tok_Tfsetuphold }
\$hold      { constTok Tok_Tfhold      }
\$recovery  { constTok Tok_Tfrecovery  }
\$removal   { constTok Tok_Tfremoval   }
\$recrem    { constTok Tok_Tfrecrem    }
\$skew      { constTok Tok_Tfskew      }
\$timeskew  { constTok Tok_Tftimeskew  }
\$fullskew  { constTok Tok_Tffullskew  }
\$period    { constTok Tok_Tfperiod    }
\$nochange  { constTok Tok_Tfnochange  }

$exp        { constTok Tok_Exp       }

-- String literals
\" @string_character* \"     { textTok (Tok_StringLit . T.drop 1 . T.init)   }

-- Identifiers
$ident_start $ident_part*      { textTok Tok_Ident }
\\ [^$white]+ $white           { textTok (Tok_Ident . T.drop 1 . T.init) }

-- Control Identifiers
\$ $ident_start $ident_part*   { textTok Tok_TaskFunction }




{
wrap :: (str -> tok) -> AlexPosn -> str -> Lexer tok
wrap f (AlexPn _ line col) s = L (line, col) (f s)

constTok = wrap . const
bstrTok f = wrap (f . T.encodeUtf8)
textTok = wrap
charTok f = wrap (f . T.head)

lexer :: String -> T.Text -> [Lexer Token]
lexer file text = go (alexStartPos, '\n', text `T.snoc` '\n')
  where
    go inp@(pos, _, cs) = case {-# SCC "alexScan" #-} alexScan inp 0 of
        AlexEOF                -> []
        AlexError inp'         -> error (errMsg inp')
        AlexSkip  inp'   _     -> go inp'
        AlexToken inp' len act -> act pos (T.take len cs) : go inp'

    errMsg (AlexPn _ line col, _, cs) =
        file ++ ": lexical error (line " ++ show line ++ ", col " ++ show col ++ ")\n"
             ++ "    near " ++ show (T.unpack $ T.take 40 cs)

-----------------------------------------------------------

type AlexInput = (AlexPosn,     -- current position,
                  Char,         -- previous char
                  T.Text)       -- current input string

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (_,c,_) = c

alexGetChar :: AlexInput -> Maybe (Char,AlexInput)
alexGetChar (p,_,cs) | T.null cs  = Nothing
                     | {-# SCC "alexSkip" #-} alexSkip c = alexGetChar (p', c, cs')
                     | otherwise  = p' `seq` cs' `seq` Just (c, (p', c, cs'))
  where
    c   = T.head cs
    cs' = T.tail cs
    p'  = alexMove p c

alexGetByte :: AlexInput -> Maybe (Int,AlexInput)
alexGetByte i = case alexGetChar i of
  Nothing -> Nothing
  Just (c, j) -> Just (ord c, j)

alexSkip :: Char -> Bool
alexSkip '\xFEFF' = True
alexSkip _        = False

-----------------------------------------------------------

data AlexPosn = AlexPn !Int !Int !Int
        deriving (Eq,Show)

alexStartPos :: AlexPosn
alexStartPos = AlexPn 0 1 1

alexMove :: AlexPosn -> Char -> AlexPosn
alexMove (AlexPn a l c) '\t' = AlexPn (a+1)  l     (((c+7) `div` 8)*8+1)
alexMove (AlexPn a l _) '\n' = AlexPn (a+1) (l+1)   1
alexMove (AlexPn a l c) _    = AlexPn (a+1)  l     (c+1)
}
