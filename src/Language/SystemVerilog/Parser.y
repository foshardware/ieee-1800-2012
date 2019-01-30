{

module Language.SystemVerilog.Parser where

import Control.Lens
import Data.Text (Text)

import Language.SystemVerilog.Syntax
import Language.SystemVerilog.Tokens

}

%name ast
%tokentype { Lexer Token }
%error { parseError }

%token

ident  { L _ (Tok_Ident _) }
xdigit { L _ (Tok_XDigit _) }
zdigit { L _ (Tok_XDigit _) }

unsignedNumber { L _ (Tok_UnsignedNumber _) }
binaryValue { L _ (Tok_BinaryValue _) }
octalValue { L _ (Tok_OctalValue _) }
hexValue { L _ (Tok_HexValue _) }

decimalBase { L _ (Tok_DecimalBase _) }
binaryBase { L _ (Tok_BinaryBase _) }
octalBase { L _ (Tok_OctalBase _) }
hexBase { L _ (Tok_HexBase _) }

stringLit { L _ (Tok_StringLit _) }


"1step" { L _ Tok_1step }
"accepton" { L _ Tok_Accepton }
"alias" { L _ Tok_Alias }
"always" { L _ Tok_Always }
"alwayscomb" { L _ Tok_Alwayscomb }
"alwaysff" { L _ Tok_Alwaysff }
"alwayslatch" { L _ Tok_Alwayslatch }
"&" { L _ Tok_Amp }
"and" { L _ Tok_And }
"&&" { L _ Tok_Andop }
"'" { L _ Tok_Apos }
"arrow" { L _ Tok_Arrow }
"^=" { L _ Tok_Asscaret }
"assert" { L _ Tok_Assert }
"assign" { L _ Tok_Assign }
"=" { L _ Tok_Assignop }
"-=" { L _ Tok_Assminus }
"%=" { L _ Tok_Asspercent }
"|=" { L _ Tok_Asspipe }
"&=" { L _ Tok_Assamp }
"+=" { L _ Tok_Assplus }
"<<=" { L _ Tok_Assshiftl }
"<<<=" { L _ Tok_Assshiftll }
">>=" { L _ Tok_Assshiftr }
">>>=" { L _ Tok_Assshiftrr }
"/=" { L _ Tok_Assslash }
"*=" { L _ Tok_Assstar }
"assume" { L _ Tok_Assume }
"at" { L _ Tok_At }
"automatic" { L _ Tok_Automatic }
"begin" { L _ Tok_Begin }
"bind" { L _ Tok_Bind }
"bins" { L _ Tok_Bins }
"binsof" { L _ Tok_Binsof }
"bit" { L _ Tok_Bit }
"break" { L _ Tok_Break }
"buf" { L _ Tok_Buf }
"bufif0" { L _ Tok_Bufif0 }
"bufif1" { L _ Tok_Bufif1 }
"byte" { L _ Tok_Byte }
"^" { L _ Tok_Caret }
"case" { L _ Tok_Case }
"casex" { L _ Tok_Casex }
"casez" { L _ Tok_Casez }
"cell" { L _ Tok_Cell }
"chandle" { L _ Tok_Chandle }
"checker" { L _ Tok_Checker }
"class" { L _ Tok_Class }
"clocking" { L _ Tok_Clocking }
"cmos" { L _ Tok_Cmos }
":" { L _ Tok_Colon }
"," { L _ Tok_Comma }
"config" { L _ Tok_Config }
"const" { L _ Tok_Const }
"constraint" { L _ Tok_Constraint }
"context" { L _ Tok_Context }
"continue" { L _ Tok_Continue }
"cover" { L _ Tok_Cover }
"covergroup" { L _ Tok_Covergroup }
"coverpoint" { L _ Tok_Coverpoint }
"cross" { L _ Tok_Cross }
"deassign" { L _ Tok_Deassign }
"--" { L _ Tok_Decrement }
"default" { L _ Tok_Default }
"defparam" { L _ Tok_Defparam }
"design" { L _ Tok_Design }
"disable" { L _ Tok_Disable }
"dist" { L _ Tok_Dist }
"do" { L _ Tok_Do }
"$" { L _ Tok_Dollar }
"." { L _ Tok_Dot }
"->>" { L _ Tok_Doublearrow }
"@@" { L _ Tok_Doubleat }
"##" { L _ Tok_Doublehash }
"**" { L _ Tok_Doublestar }
"dweq" { L _ Tok_Dweq }
"dwne" { L _ Tok_Dwne }
"edge" { L _ Tok_Edge }
"else" { L _ Tok_Else }
"end" { L _ Tok_End }
"endcase" { L _ Tok_Endcase }
"endchecker" { L _ Tok_Endchecker }
"endclass" { L _ Tok_Endclass }
"endconfig" { L _ Tok_Endconfig }
"endfunction" { L _ Tok_Endfunction }
"endgenerate" { L _ Tok_Endgenerate }
"endgroup" { L _ Tok_Endgroup }
"endinterface" { L _ Tok_Endinterface }
"endmodule" { L _ Tok_Endmodule }
"endpackage" { L _ Tok_Endpackage }
"endprimitive" { L _ Tok_Endprimitive }
"endprogram" { L _ Tok_Endprogram }
"endproperty" { L _ Tok_Endproperty }
"endsequence" { L _ Tok_Endsequence }
"endtable" { L _ Tok_Endtable }
"endtask" { L _ Tok_Endtask }
"enum" { L _ Tok_Enum }
"==" { L _ Tok_Eq }
"=>" { L _ Tok_Eqarrow }
"===" { L _ Tok_Equivalent }
"event" { L _ Tok_Event }
"eventually" { L _ Tok_Eventually }
"exp" { L _ Tok_Exp }
"expect" { L _ Tok_Expect }
"export" { L _ Tok_Export }
"extends" { L _ Tok_Extends }
"extern" { L _ Tok_Extern }
"final" { L _ Tok_Final }
"firstmatch" { L _ Tok_Firstmatch }
"followedby" { L _ Tok_Followedby }
"followedbyoverlapped" { L _ Tok_Followedbyoverlapped }
"for" { L _ Tok_For }
"force" { L _ Tok_Force }
"foreach" { L _ Tok_Foreach }
"forever" { L _ Tok_Forever }
"fork" { L _ Tok_Fork }
"function" { L _ Tok_Function }
"generate" { L _ Tok_Generate }
"genvar" { L _ Tok_Genvar }
"gt" { L _ Tok_Gt }
"gteq" { L _ Tok_Gteq }
">>" { L _ Tok_Gtgt }
"#" { L _ Tok_Hash }
"highz0" { L _ Tok_Highz0 }
"highz1" { L _ Tok_Highz1 }
"if" { L _ Tok_If }
"iff" { L _ Tok_Iff }
"ifnone" { L _ Tok_Ifnone }
"ignorebins" { L _ Tok_Ignorebins }
"illegalbins" { L _ Tok_Illegalbins }
"implements" { L _ Tok_Implements }
"implication" { L _ Tok_Implication }
"implicationoverlapped" { L _ Tok_Implicationoverlapped }
"implies" { L _ Tok_Implies }
"import" { L _ Tok_Import }
"incdir" { L _ Tok_Incdir }
"include" { L _ Tok_Include }
"++" { L _ Tok_Increment }
"initial" { L _ Tok_Initial }
"inout" { L _ Tok_Inout }
"input" { L _ Tok_Input }
"inside" { L _ Tok_Inside }
"instance" { L _ Tok_Instance }
"int" { L _ Tok_Int }
"integer" { L _ Tok_Integer }
"interconnect" { L _ Tok_Interconnect }
"interface" { L _ Tok_Interface }
"intersect" { L _ Tok_Intersect }
"join" { L _ Tok_Join }
"joinany" { L _ Tok_Joinany }
"joinnone" { L _ Tok_Joinnone }
"large" { L _ Tok_Large }
"{" { L _ Tok_Lbrace }
"[" { L _ Tok_Lbracket }
"let" { L _ Tok_Let }
"liblist" { L _ Tok_Liblist }
"library" { L _ Tok_Library }
"local" { L _ Tok_Local }
"localparam" { L _ Tok_Localparam }
"logic" { L _ Tok_Logic }
"longint" { L _ Tok_Longint }
"(" { L _ Tok_Lparen }
"lt" { L _ Tok_Lt }
"lteq" { L _ Tok_Lteq }
"<<" { L _ Tok_Ltlt }
"macromodule" { L _ Tok_Macromodule }
"matches" { L _ Tok_Matches }
"medium" { L _ Tok_Medium }
"-" { L _ Tok_Minus }
"modport" { L _ Tok_Modport }
"module" { L _ Tok_Module }
"::" { L _ Tok_Namequal }
"nand" { L _ Tok_Nand }
"negedge" { L _ Tok_Negedge }
"nettype" { L _ Tok_Nettype }
"new" { L _ Tok_New }
"nexttime" { L _ Tok_Nexttime }
"nmos" { L _ Tok_Nmos }
"nor" { L _ Tok_Nor }
"noshowcancelled" { L _ Tok_Noshowcancelled }
"not" { L _ Tok_Not }
"!=" { L _ Tok_Noteq }
"!==" { L _ Tok_Notequivalent }
"notif0" { L _ Tok_Notif0 }
"notif1" { L _ Tok_Notif1 }
"!" { L _ Tok_Notop }
"null" { L _ Tok_Null }
"option" { L _ Tok_Option }
"or" { L _ Tok_Or }
"||" { L _ Tok_Orop }
"output" { L _ Tok_Output }
"package" { L _ Tok_Package }
"packed" { L _ Tok_Packed }
"parameter" { L _ Tok_Parameter }
"pathpulse" { L _ Tok_Pathpulse }
"%" { L _ Tok_Percent }
"|" { L _ Tok_Pipe }
"+" { L _ Tok_Plus }
"pmos" { L _ Tok_Pmos }
"posedge" { L _ Tok_Posedge }
"primitive" { L _ Tok_Primitive }
"priority" { L _ Tok_Priority }
"program" { L _ Tok_Program }
"property" { L _ Tok_Property }
"protected" { L _ Tok_Protected }
"pull0" { L _ Tok_Pull0 }
"pull1" { L _ Tok_Pull1 }
"pulldown" { L _ Tok_Pulldown }
"pullup" { L _ Tok_Pullup }
"pulsestyleondetect" { L _ Tok_Pulsestyleondetect }
"pulsestyleonevent" { L _ Tok_Pulsestyleonevent }
"pure" { L _ Tok_Pure }
"?" { L _ Tok_Question }
"rand" { L _ Tok_Rand }
"randc" { L _ Tok_Randc }
"randcase" { L _ Tok_Randcase }
"randomize" { L _ Tok_Randomize }
"randsequence" { L _ Tok_Randsequence }
"}" { L _ Tok_Rbrace }
"]" { L _ Tok_Rbracket }
"rcmos" { L _ Tok_Rcmos }
"real" { L _ Tok_Real }
"realtime" { L _ Tok_Realtime }
"ref" { L _ Tok_Ref }
"reg" { L _ Tok_Reg }
"rejecton" { L _ Tok_Rejecton }
"release" { L _ Tok_Release }
"repeat" { L _ Tok_Repeat }
"restrict" { L _ Tok_Restrict }
"rnmos" { L _ Tok_Rnmos }
"$root" { L _ Tok_Rootscope }
")" { L _ Tok_Rparen }
"rpmos" { L _ Tok_Rpmos }
"rtran" { L _ Tok_Rtran }
"rtranif0" { L _ Tok_Rtranif0 }
"rtranif1" { L _ Tok_Rtranif1 }
"salways" { L _ Tok_Salways }
"sample" { L _ Tok_Sample }
"scalared" { L _ Tok_Scalared }
";" { L _ Tok_Semi }
"sequence" { L _ Tok_Sequence }
"seventually" { L _ Tok_Seventually }
"shortint" { L _ Tok_Shortint }
"shortreal" { L _ Tok_Shortreal }
"showcancelled" { L _ Tok_Showcancelled }
"signed" { L _ Tok_Signed }
"/" { L _ Tok_Slash }
"small" { L _ Tok_Small }
"snexttime" { L _ Tok_Snexttime }
"soft" { L _ Tok_Soft }
"solve" { L _ Tok_Solve }
"specify" { L _ Tok_Specify }
"specparam" { L _ Tok_Specparam }
"*" { L _ Tok_Star }
"static" { L _ Tok_Static }
"std" { L _ Tok_Std }
"string" { L _ Tok_String }
"strong" { L _ Tok_Strong }
"strong0" { L _ Tok_Strong0 }
"strong1" { L _ Tok_Strong1 }
"struct" { L _ Tok_Struct }
"suntil" { L _ Tok_Suntil }
"suntilwith" { L _ Tok_Suntilwith }
"super" { L _ Tok_Super }
"supply0" { L _ Tok_Supply0 }
"supply1" { L _ Tok_Supply1 }
"syncrejecton" { L _ Tok_Syncrejecton }
"table" { L _ Tok_Table }
"tagged" { L _ Tok_Tagged }
"task" { L _ Tok_Task }
"tffullskew" { L _ Tok_Tffullskew }
"tfhold" { L _ Tok_Tfhold }
"tfnochange" { L _ Tok_Tfnochange }
"tfperiod" { L _ Tok_Tfperiod }
"tfrecovery" { L _ Tok_Tfrecovery }
"tfrecrem" { L _ Tok_Tfrecrem }
"tfremoval" { L _ Tok_Tfremoval }
"tfsetup" { L _ Tok_Tfsetup }
"tfsetuphold" { L _ Tok_Tfsetuphold }
"tfskew" { L _ Tok_Tfskew }
"tftimeskew" { L _ Tok_Tftimeskew }
"this" { L _ Tok_This }
"throughout" { L _ Tok_Throughout }
"~" { L _ Tok_Tilde }
"time" { L _ Tok_Time }
"timeprecision" { L _ Tok_Timeprecision }
"timeunit" { L _ Tok_Timeunit }
"tran" { L _ Tok_Tran }
"tranif0" { L _ Tok_Tranif0 }
"tranif1" { L _ Tok_Tranif1 }
"tri" { L _ Tok_Tri }
"tri0" { L _ Tok_Tri0 }
"tri1" { L _ Tok_Tri1 }
"triand" { L _ Tok_Triand }
"trior" { L _ Tok_Trior }
"&&&" { L _ Tok_Tripleamp }
"trireg" { L _ Tok_Trireg }
"type" { L _ Tok_Type }
"typedef" { L _ Tok_Typedef }
"typeoption" { L _ Tok_Typeoption }
"union" { L _ Tok_Union }
"unique" { L _ Tok_Unique }
"unique0" { L _ Tok_Unique0 }
"unitscope" { L _ Tok_Unitscope }
"unsigned" { L _ Tok_Unsigned }
"until" { L _ Tok_Until }
"untilwith" { L _ Tok_Untilwith }
"untyped" { L _ Tok_Untyped }
"use" { L _ Tok_Use }
"uwire" { L _ Tok_Uwire }
"var" { L _ Tok_Var }
"vectored" { L _ Tok_Vectored }
"virtual" { L _ Tok_Virtual }
"void" { L _ Tok_Void }
"wait" { L _ Tok_Wait }
"waitorder" { L _ Tok_Waitorder }
"wand" { L _ Tok_Wand }
"weak" { L _ Tok_Weak }
"weak0" { L _ Tok_Weak0 }
"weak1" { L _ Tok_Weak1 }
"while" { L _ Tok_While }
"wildcard" { L _ Tok_Wildcard }
"wire" { L _ Tok_Wire }
"with" { L _ Tok_With }
"within" { L _ Tok_Within }
"wor" { L _ Tok_Wor }
"xnor" { L _ Tok_Xnor }
"xor" { L _ Tok_Xor }

%%


ast :: { AST }
: LibraryText { LibraryText_AST $1 }
| SourceText { SourceText_AST $1 } 


-- | A.1 Source text
--
--  A.1.1 Library source text
--

LibraryText :: { LibraryText }
: many1(LibraryDescription) { LibraryText $1 }

LibraryDescription :: { LibraryDescription }
: LibraryDeclaration { LibraryDeclaration_LibraryDescription $1 }
| IncludeStatement { IncludeStatement_LibraryDescription $1 }
-- | ConfigDeclaration { ConfigDeclaration_LibraryDescription $1 }
| ";" { NoLibraryDescription }

LibraryDeclaration :: { LibraryDeclaration }
: "library"
  LibraryIdentifier
  sepBy1(FilePathSpec, ",")
  opt(third("-", "incdir", sepBy1(FilePathSpec, ",")))
  ";"
  { LibraryDeclaration $2 $3 $4 }

IncludeStatement :: { IncludeStatement }
: "include" FilePathSpec ";" { IncludeStatement $2 }


-- | A.1.2 SystemVerilog source text
--

SourceText :: { SourceText }
: opt(TimeunitsDeclaration) many1(Description) { SourceText $1 $2 }

Description :: { Description }
: ModuleDeclaration { ModuleDeclaration_Description $1 }
-- | UdpDeclaration { UdpDeclaration_Description $1 }
-- | InterfaceDeclaration { InterfaceDeclaration_Description $1 }
-- | ProgramDeclaration { ProgramDeclaration_Description $1 }
-- | PackageDeclaration { PackageDeclaration_Description $1 }
-- | many(AttributeInstance) PackageItem { PackageItem_Description $1 $2 }
-- | many(AttributeInstance) BindDirective { BindDirective_Description $1 $2 }
-- | ConfigDeclaration { ConfigDeclaration_Description $1 }


ModuleNonAnsiHeader :: { ModuleNonAnsiHeader }
: many(AttributeInstance) ModuleKeyword opt(Lifetime) ModuleIdentifier
  many(PackageImportDeclaration) opt(ParameterPortList) ListOfPorts ";"
  { ModuleNonAnsiHeader $1 $2 $3 $4 $5 $6 $7 }


ModuleAnsiHeader :: { ModuleAnsiHeader }
: many(AttributeInstance) ModuleKeyword opt(Lifetime) ModuleIdentifier
  many(PackageImportDeclaration) opt(ParameterPortList) opt(ListOfPortDeclarations) ";"
  { ModuleAnsiHeader $1 $2 $3 $4 $5 $6 $7 }


ModuleDeclaration :: { ModuleDeclaration }
: ModuleNonAnsiHeader
  opt(TimeunitsDeclaration)
  many(ModuleItem)
  "endmodule"
  opt(second(":", ModuleIdentifier))
  { ModuleNonAnsiHeader_ModuleDeclaration $1 $2 $3 $5 }
| ModuleAnsiHeader
  opt(TimeunitsDeclaration)
  many(NonPortModuleItem)
  "endmodule"
  opt(second(":", ModuleIdentifier))
  { ModuleAnsiHeader_ModuleDeclaration $1 $2 $3 $5 }
| many(AttributeInstance)
  ModuleKeyword opt(Lifetime) ModuleIdentifier "(" "." "*" ")" ";"
  opt(TimeunitsDeclaration)
  many(ModuleItem)
  "endmodule"
  opt(second(":", ModuleIdentifier))
  { ModuleDeclaration $1 $2 $3 $4 $10 $11 $13 }
| "extern" ModuleNonAnsiHeader { ExternModuleNonAnsiHeader_ModuleDeclaration $2 }
| "extern" ModuleAnsiHeader { ExternModuleAnsiHeader_ModuleDeclaration $2 }


ModuleKeyword :: { ModuleKeyword }
: "module" { Module }
| "macromodule" { Macromodule }


TimeunitsDeclaration :: { TimeunitsDeclaration }
: "timeunit" TimeLiteral opt(second("/", TimeLiteral)) ";"
  { TimeunitsDeclaration (Just $2) $3 }
| "timeprecision" TimeLiteral ";"
  { TimeunitsDeclaration Nothing (Just $2) }
| "timeunit" TimeLiteral ";"
  "timeprecision" TimeLiteral ";"
  { TimeunitsDeclaration (Just $2) (Just $5) }
| "timeprecision" TimeLiteral ";"
  "timeunit" TimeLiteral ";"
  { TimeunitsDeclaration (Just $5) (Just $2) }


-- | A.1.3 Module parameters and ports
--

ParameterPortList :: { ParameterPortList }
: "#" "(" opt(ListOfParamAssignments) sepBy(ParameterPortDeclaration, ",") ")"
  { ParameterPortList $3 $4 }

ParameterPortDeclaration :: { ParameterPortDeclaration }
: ParameterDeclaration { ParameterDeclaration_ParameterPortDeclaration $1 }
| LocalParameterDeclaration { LocalParameterDeclaration_ParameterPortDeclaration $1 }
| DataType ListOfParamAssignments { DataType_ParameterPortDeclaration $1 $2 }
| "type" ListOfTypeAssignments { TypeAssignments_ParameterPortDeclaration $2 }


ListOfPorts :: { [Port] }
: "(" sepBy1(Port, ",") ")" { $2 }


ListOfPortDeclarations :: { ListOfPortDeclarations }
: "(" opt(sepBy1(tuple(many(AttributeInstance), AnsiPortDeclaration), ",")) ")"
  { $2 }


PortDeclaration :: { PortDeclaration }
: many(AttributeInstance) InoutDeclaration { InoutDeclaration_PortDeclaration $1 $2 }
| many(AttributeInstance) InputDeclaration { InputDeclaration_PortDeclaration $1 $2 }
| many(AttributeInstance) OutputDeclaration { OutputDeclaration_PortDeclaration $1 $2 }
-- | many(AttributeInstance) RefDeclaration { RefDeclaration_PortDeclaration $1 $2 }
-- | many(AttributeInstance) InterfacePortDeclaration { InterfacePortDeclaration_PortDeclaration $1 $2 }


Port :: { Port }
: second(".", PortIdentifier) "(" opt(PortExpression) ")"
  { Port (Just $1) $3 }
| opt(PortExpression)
  { Port Nothing $1 }


PortExpression :: { [PortReference] }
: sepBy1(PortReference, ",") { $1 }


PortReference :: { PortReference }
: PortIdentifier ConstantSelect { PortReference $1 $2 }


PortDirection :: { PortDirection }
: "inout" { Inout }
| "input" { Input }
| "output" { Output }
| "ref" { Ref }


NetPortHeader :: { NetPortHeader }
: opt(PortDirection) NetPortType { NetPortHeader $1 $2 }

VariablePortHeader :: { VariablePortHeader }
: opt(PortDirection) VariablePortType { VariablePortHeader $1 $2 }

InterfacePortHeader :: { InterfacePortHeader }
: "interface" opt(second(".", ModportIdentifier))
  { InterfacePortHeader Nothing $2 }
| InterfaceIdentifier opt(second(".", ModportIdentifier))
  { InterfacePortHeader (pure $1) $2 }


AnsiPortDeclaration :: { AnsiPortDeclaration }
: opt(NetPortHeader) PortIdentifier many(UnpackedDimension) opt(second("=", ConstantExpression))
  { NetPortHeader_AnsiPortDeclaration $1 $2 $3 $4 }
| opt(InterfacePortHeader) PortIdentifier many(UnpackedDimension) opt(second("=", ConstantExpression))
  { InterfacePortHeader_AnsiPortDeclaration $1 $2 $3 $4 }
| opt(VariablePortHeader) PortIdentifier many(VariableDimension) opt(second("=", ConstantExpression))
  { VariablePortHeader_AnsiPortDeclaration $1 $2 $3 $4 }
| opt(PortDirection) "." PortIdentifier "(" opt(Expression) ")"
  { AnsiPortDeclaration $1 $3 $5 }


-- | A.1.4 Module items
--

ModuleItem :: { ModuleItem }
: PortDeclaration ";" { PortDeclaration_ModuleItem $1 }
| NonPortModuleItem { NonPortModuleItem_ModuleItem $1 }


NonPortModuleItem :: { NonPortModuleItem }
-- : GenerateRegion { GenerateRegion_NonPortModuleItem $1 }
-- | ModuleOrGenerateItem { ModuleOrGenerateItem_NonPortModuleItem $1 }
-- | SpecifyBlock { SpecifyBlock_NonPortModuleItem $1 }
-- | SpecparamDeclaration { SpecparamDeclaration_NonPortModuleItem $1 }
-- | ProgramDeclaration { ProgramDeclaration_NonPortModuleItem $1 }
: ModuleDeclaration { ModuleDeclaration_NonPortModuleItem $1 }
-- | InterfaceDeclaration { InterfaceDeclaration_NonPortModuleItem $1 }
| TimeunitsDeclaration { TimeunitsDeclaration_NonPortModuleItem $1 }



-- | A.1.9 Class items
--

RandomQualifier :: { RandomQualifier }
: "rand"  { Rand  }
| "randc" { Randc }


-- | A.2 Declarations
--
--   A.2.1 Declaration types
--
--   A.2.1.1 Module parameter declarations
--

LocalParameterDeclaration :: { LocalParameterDeclaration }
: "localparam" DataTypeOrImplicit ListOfParamAssignments
  { DataTypeOrImplicit_LocalParameterDeclaration $2 $3 }
| "localparam" "type" ListOfTypeAssignments
  { ListOfTypeAssignments_LocalParameterDeclaration $3 }


ParameterDeclaration :: { ParameterDeclaration }
: "parameter" DataTypeOrImplicit ListOfParamAssignments
  { DataTypeOrImplicit_ParameterDeclaration $2 $3 }
| "parameter" "type" ListOfTypeAssignments
  { ListOfTypeAssignments_ParameterDeclaration $3 }


Lifetime :: { Lifetime }
: "static" { StaticLifetime }
| "automatic" { AutomaticLifetime }


-- | A.2.1.2 Port declarations
--

InoutDeclaration :: { InoutDeclaration }
: "inout" NetPortType ListOfPortIdentifiers { InoutDeclaration $2 $3 }

InputDeclaration :: { InputDeclaration }
: "input" either(NetPortType, VariablePortType) ListOfPortIdentifiers { InputDeclaration $2 $3 }

OutputDeclaration :: { OutputDeclaration }
: "output" either(NetPortType, VariablePortType) ListOfPortIdentifiers { OutputDeclaration $2 $3 }


-- | A.2.1.3  Type declarations
--

PackageImportDeclaration :: { PackageImportDeclaration }
: "import" sepBy1(PackageImportItem, ",") ";" { $2 }

PackageImportItem :: { PackageImportItem }
: PackageIdentifier "::" Identifier { PackageImportItem $1 (Just $3) }
| PackageIdentifier "::" "*" { PackageImportItem $1 Nothing }





-- | A.2.2 Declaration types
--
--   A.2.2.1 Net and variable types
--

CastingType :: { CastingType }
: SimpleType { SimpleType_CastingType $1 }
| ConstantPrimary { ConstantPrimary_CastingType $1 }
| Signing { Signing_CastingType $1 }
| "string" { StringCastingType }
| "const" { ConstCastingType }


DataType :: { DataType }
: IntegerVectorType opt(Signing) many(PackedDimension)
  { IntegerVectorType_DataType $1 $2 $3 }
| IntegerAtomType opt(Signing)
  { IntegerAtomType_DataType $1 $2 }
| NonIntegerType { NonIntegerType_DataType $1 }
| StructUnion
  opt(second("packed", opt(Signing)))
  "(" many1(StructUnionMember) ")"
  many(PackedDimension)
  { StructUnion_DataType $1 $2 $4 $6 }
| opt(EnumBaseType)
  "(" sepBy1(EnumNameDeclaration, ",") ")"
  many(PackedDimension)
  { Enum_DataType $1 $3 $5 }
| "string" { StringDataType }
| "chandle" { ChandleDataType }
| "virtual" opt("interface")
  InterfaceIdentifier
  opt(ParameterValueAssignment)
  opt(ModportIdentifier)
  { Interface_DataType (() <$ $2) $3 $4 $5 }
| opt(either(ClassScope, PackageScope))
  TypeIdentifier
  many(PackedDimension)
  { Type_DataType $1 $2 $3 }
| ClassType { ClassType_DataType $1 }
| "event" { EventDataType }
| PsCovergroupIdentifier { PsCovergroup_DataType $1 }
| TypeReference { TypeReference_DataType $1 }


DataTypeOrImplicit :: { DataTypeOrImplicit }
: DataType { DataType_DataTypeOrImplicit $1 }
| ImplicitDataType { ImplicitDataType_DataTypeOrImplicit $1 }


ImplicitDataType :: { ImplicitDataType }
: opt(Signing) many(PackedDimension) { ImplicitDataType $1 $2 }


EnumBaseType :: { EnumBaseType }
: IntegerAtomType opt(Signing) { IntegerAtomType_EnumBaseType $1 $2 }
| IntegerVectorType opt(Signing) opt(PackedDimension)
  { IntegerVectorType_EnumBaseType $1 $2 $3 }
| TypeIdentifier opt(PackedDimension) { Type_EnumBaseType $1 $2 }


EnumNameDeclaration :: { EnumNameDeclaration }
: EnumIdentifier
  opt(between("[", "]", tuple(IntegralNumber, opt(second(";", IntegralNumber)))))
  opt(second("=", ConstantExpression))
  { EnumNameDeclaration $1 $2 $3 }


ClassScope :: { ClassScope }
: ClassType "::" { $1 }

ClassType :: { ClassType }
: PsClassIdentifier
  opt(ParameterValueAssignment)
  many(second("::", tuple(ClassIdentifier, opt(ParameterValueAssignment))))
  { ClassType $1 $2 $3 }


IntegerType :: { IntegerType }
: IntegerVectorType { IntegerVectorType_IntegerType $1 }
| IntegerAtomType { IntegerAtomType_IntegerType $1 }


IntegerAtomType :: { IntegerAtomType }
: "byte"     { TByte     }
| "shortint" { TShortint }
| "int"      { TInt      }
| "longint"  { TLongint  }
| "integer"  { TInteger  }
| "time"     { TTime     }


IntegerVectorType :: { IntegerVectorType }
: "bit"   { TBit   }
| "logic" { TLogic }
| "reg"   { TReg   }


NonIntegerType :: { NonIntegerType }
: "shortreal" { TShortreal }
| "real"      { TReal      }
| "realtime"  { TRealtime  }


NetType :: { NetType }
: "supply0" { TSupply0 }
| "supply1" { TSupply1 }
| "tri"     { Tri }
| "triand"  { Triand }
| "trior"   { Trior }
| "trireg"  { Trireg }
| "tri0"    { Tri0 }
| "tri1"    { Tri1 }
| "uwire"   { Uwire }
| "wire"    { Wire }
| "wand"    { Wand }
| "wor"     { Wor }


NetPortType :: { NetPortType }
: opt(NetType) DataTypeOrImplicit { DataTypeOrImplicit_NetPortType $1 $2 }
| NetTypeIdentifier { NetType_NetPortType $1 }
| "interconnect" ImplicitDataType { ImplicitDataType_NetPortType $2 }


VariablePortType :: { VariablePortType }
: VarDataType { $1 }


VarDataType :: { VarDataType }
: DataType { DataType_VarDataType $1 }
| "var" DataTypeOrImplicit { DataTypeOrImplicit_VarDataType $2 }


Signing :: { Signing }
: "signed"   { Signed   }
| "unsigned" { Unsigned }


SimpleType :: { SimpleType }
: IntegerType { IntegerType_SimpleType $1 }
| NonIntegerType { NonIntegerType_SimpleType $1 }
| PsTypeIdentifier { PsType_SimpleType $1 }
| PsParameterIdentifier { PsParameter_SimpleType $1 }


StructUnionMember :: { StructUnionMember }
: many(AttributeInstance)
  opt(RandomQualifier)
  DataTypeOrVoid
  ListOfVariableDeclAssignments
  ";"
  { StructUnionMember $1 $2 $3 $4 }


DataTypeOrVoid :: { DataTypeOrVoid }
: DataType { DataType_DataTypeOrVoid $1 }
| "void" { VoidDataType }


StructUnion :: { StructUnion }
: "struct"               { TStruct }
| "union" opt("tagged")  { TUnion (() <$ $2) }


TypeReference :: { TypeReference }
: "type" "(" Expression ")" { Expression_TypeReference $3 }
| "type" "(" DataType ")" { DataType_TypeReference $3 }



-- | A.2.3 Declaration lists
--

ListOfParamAssignments :: { ListOfParamAssignments }
: sepBy1(ParamAssignment, ",") { $1 }

ListOfPortIdentifiers :: { ListOfPortIdentifiers }
: sepBy1(tuple(PortIdentifier, many(UnpackedDimension)), ",") { $1 }

ListOfTypeAssignments :: { ListOfTypeAssignments }
: sepBy1(TypeAssignment, ",") { $1 }

ListOfVariableDeclAssignments :: { ListOfVariableDeclAssignments }
: sepBy1(VariableDeclAssignment, ",") { $1 }


-- | A.2.4 Declaration assignments
--

ParamAssignment :: { ParamAssignment }
: ParameterIdentifier many(UnpackedDimension) opt(second("=", ConstantParamExpression))
  { ParamAssignment $1 $2 $3 }


TypeAssignment :: { TypeAssignment }
: TypeIdentifier opt(second("=", DataType))
  { TypeAssignment $1 $2 }


VariableDeclAssignment :: { VariableDeclAssignment }
: VariableIdentifier many(VariableDimension) opt(second("=", Expression))
  { VariableDeclAssignment $1 $2 $3 }
| DynamicArrayVariableIdentifier UnsizedDimension many(VariableDimension) opt(second("=", DynamicArrayNew))
  { DynamicArrayVariableIdentifier_VariableDeclAssignment $1 $2 $3 $4 }
| ClassVariableIdentifier opt(second("=", ClassNew))
  { ClassVariableIdentifier_VariableDeclAssignment $1 $2 }

ClassNew :: { ClassNew }
: opt(ClassScope) "new" opt(between("(", ")", ListOfArguments))
  { ClassNew $1 $3 }
| "new" Expression
  { Expression_ClassNew $2 }


DynamicArrayNew :: { DynamicArrayNew }
: "new" "[" Expression "]" opt(between("(", ")", Expression))
  { DynamicArrayNew $3 $5 }



-- | A.2.5 Declaration ranges
--

UnpackedDimension :: { UnpackedDimension }
: "[" ConstantRange "]" { ConstantRange_UnpackedDimension $2 }
| "[" ConstantExpression "]" { ConstantExpression_UnpackedDimension $2 }

PackedDimension :: { PackedDimension }
: "[" ConstantRange "]" { ConstantRange_PackedDimension $2 }
| "[" UnsizedDimension "]" { UnsizedDimension_PackedDimension $2 }


AssociativeDimension :: { AssociativeDimension }
: "[" DataType "]" { Just $2 }
| "[" "*" "]" { Nothing }

VariableDimension :: { VariableDimension }
: UnsizedDimension { UnsizedDimension_VariableDimension $1 }
| UnpackedDimension { UnpackedDimension_VariableDimension $1 }
| AssociativeDimension { AssociativeDimension_VariableDimension $1 }
| QueueDimension { QueueDimension_VariableDimension $1 }

QueueDimension :: { QueueDimension }
: "[" "$" opt(second(":", ConstantExpression)) "]" { $3 }

UnsizedDimension :: { UnsizedDimension }
: "[" "]" { () }


-- | A.2.10 Assertion declarations
--


-- SequenceMethodCall :: { SequenceMethodCall }
-- : SequenceInstance "." MethodIdentifier { SequenceMethodCall $1 $3 }


LetExpression :: { LetExpression }
: opt(PackageScope) LetIdentifier opt(between("(", ")", opt(LetListOfArguments)))
  { LetExpression $1 $2 $3 }


LetListOfArguments :: { LetListOfArguments }
: sepBy(opt(LetActualArg), ",")
  opt(second(",", sepBy(tuple(second(".", Identifier), between("(", ")", opt(LetActualArg))), ",")))
  { LetListOfArguments $1 $2 }
| sepBy1(tuple(second(".", Identifier), between("(", ")", opt(LetActualArg))), ",")
  { LetListOfArguments [] (Just $1) }

LetActualArg :: { LetActualArg }
: Expression { $1 }


-- | A.2.11 Covergroup declarations
--



-- | A.4 Instantiations
--
--   A.4.1 Instantiation
--
--   A.4.1.1 Module instantiation
--


ParameterValueAssignment :: { ParameterValueAssignment }
: "#" "(" opt(ListOfParameterAssignments)  ")" { $3 }


ListOfParameterAssignments :: { ListOfParameterAssignments }
: sepBy1(OrderedParameterAssignment, ",") { Left $1 }
| sepBy1(NamedParameterAssignment, ",") { Right $1 }


OrderedParameterAssignment :: { OrderedParameterAssignment }
: ParamExpression { $1 }

NamedParameterAssignment :: { NamedParameterAssignment }
: "." ParameterIdentifier "(" opt(ParamExpression) ")" { ($2, $4) }


OpenRangeList :: { OpenRangeList }
: sepBy1(OpenValueRange, ",") { $1 }

OpenValueRange :: { OpenValueRange }
: ValueRange { $1 }


-- | A.6.2 Procedural blocks and assignments
--

OperatorAssignment :: { OperatorAssignment }
: VariableLvalue AssignmentOperator Expression
  { OperatorAssignment $1 $2 $3 }


AssignmentOperator :: { AssignmentOperator }
: "="  { Ass }
| "+=" { AssPlus }
| "-=" { AssMinus }
| "*=" { AssStar }
| "%=" { AssPercent }
| "&=" { AssAmp }
| "|=" { AssPipe }
| "^=" { AssCaret }
| "<<=" { AssShiftL }
| ">>=" { AssShiftR }
| "<<<=" { AssShiftLL }
| ">>>=" { AssShiftRR }


-- | A.6.6 Conditional statements
--

CondPredicate :: { CondPredicate }
: sepBy1(ExpressionOrCondPattern, "&&&") { CondPredicate $1 }


ExpressionOrCondPattern :: { ExpressionOrCondPattern }
: Expression { Left $1 }
| CondPattern { Right $1 }


CondPattern :: { CondPattern }
: Expression "matches" Pattern
  { CondPattern $1 $3 }



-- | A.6.7.1 Patterns
--


-- | A.6.7.1 Patterns
--

Pattern :: { Pattern }
: "." VariableIdentifier { VariableIdentifier_Pattern $2 }
| "." "*" { WildcardPattern }
| ConstantExpression { ConstantExpression_Pattern $1 }
| "tagged" MemberIdentifier opt(Pattern)
  { TaggedPattern $2 $3 }
| "'" "{" sepBy1(Pattern, ",") "}"
  { PatternList_Pattern $3 }
| "'" "{" sepBy1(tuple(MemberIdentifier, second(":", Pattern)), ",")  "}"
  { MemberList_Pattern $3 }


AssignmentPattern :: { AssignmentPattern }
: "'" "{" sepBy1(Expression, ",") "}"
  { ExpressionList_AssignmentPattern $3 }
| "'" "{" sepBy1(tuple(StructurePatternKey, second(":", Expression)), ",") "}"
  { StructurePatternKeyList_AssignmentPattern $3 }
| "'" "{" sepBy1(tuple(ArrayPatternKey, second(":", Expression)), ",") "}"
  { ArrayPatternKeyList_AssignmentPattern $3 }
| "'" "{" ConstantExpression "{" sepBy1(Expression, ",") "}" "}"
  { ConstantExpression_AssignmentPattern $3 $5 }


StructurePatternKey :: { StructurePatternKey }
: MemberIdentifier { Left $1 }
| AssignmentPatternKey { Right $1 }

ArrayPatternKey :: { ArrayPatternKey }
: ConstantExpression { Left $1 }
| AssignmentPatternKey { Right $1 }

AssignmentPatternKey :: { AssignmentPatternKey }
: SimpleType { Just $1 }
| "default" { Nothing }


AssignmentPatternExpression :: { AssignmentPatternExpression }
: opt(AssignmentPatternExpressionType) AssignmentPattern
  { AssignmentPatternExpression $1 $2 }


AssignmentPatternExpressionType :: { AssignmentPatternExpressionType }
: PsTypeIdentifier { PsTypeIdentifier_AssignmentPatternExpressionType $1 }
| PsParameterIdentifier { PsParameterIdentifier_AssignmentPatternExpressionType $1 }
| IntegerAtomType { IntegerAtomType_AssignmentPatternExpressionType $1 }
| TypeReference { TypeReference_AssignmentPatternExpressionType $1 }


ConstantAssignmentPatternExpression :: { ConstantAssignmentPatternExpression }
: AssignmentPatternExpression { $1 }

-- AssignmentPatternNetLvalue :: { AssignmentPatternNetLvalue }
-- : "'" "[" sepBy1(NetLvalue, ",") "]" { $3 }

AssignmentPatternVariableLvalue :: { AssignmentPatternVariableLvalue }
: "'" "[" sepBy1(VariableLvalue, ",") "]" { $3 }


-- | A.8 Expressions
--
--   A.8.1 Concatenations
--

Concatenation :: { Concatenation }
: "{" sepBy1(Expression, ",") "}" { $2 }


ConstantConcatenation :: { ConstantConcatenation }
: "{" sepBy1(ConstantExpression, ",") "}" { $2 }


ConstantMultipleConcatenation :: { ConstantMultipleConcatenation }
: "{" ConstantExpression ConstantConcatenation "}"
  { ConstantMultipleConcatenation $2 $3 }


MultipleConcatenation :: { MultipleConcatenation }
: "{" Expression Concatenation "}"
  { MultipleConcatenation $2 $3 }


StreamingConcatenation :: { StreamingConcatenation }
: "{" StreamOperator opt(SliceSize) StreamConcatenation "}"
  { StreamingConcatenation $2 $3 $4 }


StreamOperator :: { StreamOperator }
: ">>" { Downstream }
| "<<" { Upstream }


SliceSize :: { SliceSize }
: SimpleType { SimpleType_SliceSize $1 }
| ConstantExpression { ConstantExpression_SliceSize $1 }


StreamConcatenation :: { StreamConcatenation }
: "{" sepBy1(StreamExpression, ",") "}" { $2 }

StreamExpression :: { StreamExpression }
: Expression opt(second("with", between("[", "]", ArrayRangeExpression)))
  { StreamExpression $1 $2 }

ArrayRangeExpression :: { ArrayRangeExpression }
: Expression ":" Expression { ArrayRangeZ $1 $3 }
| Expression "+" ":" Expression { ArrayRangeP $1 $4 }
| Expression "-" ":" Expression { ArrayRangeM $1 $4 }
| Expression { Expression_ArrayRangeExpression $1 }


EmptyQueue :: { EmptyQueue }
: "[" "]" { EmptyQueue }



-- | A.8.2 Subroutine calls
--

ListOfArguments :: { ListOfArguments }
: sepBy1(opt(Expression), ",")
  sepBy(tuple(second(".", Identifier), between("(", ")", opt(Expression))), ",")
  { ListOfArguments (Just $1) $2 }
| sepBy1(tuple(second(".", Identifier), between("(", ")", opt(Expression))), ",")
  { ListOfArguments Nothing $1 }





-- | A.8.3 Expressions
--

IncOrDecExpression :: { IncOrDecExpression }
: IncOrDecOperator many(AttributeInstance) VariableLvalue
  { PrefixIncOrDecExpression $1 $2 $3 }
| VariableLvalue many(AttributeInstance) IncOrDecOperator
  { PostfixIncOrDecExpression $1 $2 $3 }


ConditionalExpression :: { ConditionalExpression }
: CondPredicate "?" many(AttributeInstance) Expression ":" Expression
  { ConditionalExpression $1 $3 $4 $6 }


ConstantExpression :: { ConstantExpression }
: ConstantPrimary { ConstantPrimary_ConstantExpression $1 }
| UnaryOperator many(AttributeInstance) ConstantPrimary
  { UnaryConstantExpression $1 $2 $3 }
| ConstantExpression BinaryOperator many(AttributeInstance) ConstantExpression
  { BinaryConstantExpression $1 $2 $3 $4 }
| ConstantExpression "?" many(AttributeInstance) ConstantExpression ":" ConstantExpression
  { TernaryConstantExpression $1 $3 $4 $6 }


ConstantMintypmaxExpression :: { ConstantMintypmaxExpression }
: ConstantExpression ":" ConstantExpression ":" ConstantExpression { Right ($1, $3, $5) }
| ConstantExpression { Left $1 }


ConstantParamExpression :: { ConstantParamExpression }
: ConstantMintypmaxExpression { ConstantMintypmaxExpression_ConstantParamExpression $1 }
| DataType { DataType_ConstantParamExpression $1 }
| "$" { DollarConstantParamExpression }


ParamExpression :: { ParamExpression }
: MintypmaxExpression { MintypmaxExpression_ParamExpression $1 }
| DataType { DataType_ParamExpression $1 }
| "$" { DollarParamExpression }


ConstantRangeExpression :: { ConstantRangeExpression }
: ConstantExpression { Left $1 }
| ConstantPartSelectRange { Right $1 }


ConstantPartSelectRange :: { ConstantPartSelectRange }
: ConstantRange { Left $1 }
| ConstantIndexedRange { Right $1 }


ConstantRange :: { ConstantRange }
: ConstantExpression ":" ConstantExpression { ($1, $3) }


ConstantIndexedRange :: { ConstantIndexedRange }
: ConstantExpression "+" ":" ConstantExpression
  { PlusConstantIndexedRange $1 $4 }
| ConstantExpression "-" ":" ConstantExpression
  { MinusConstantIndexedRange $1 $4 }


Expression :: { Expression }
: Primary { Primary_Expression $1 }
| UnaryOperator many(AttributeInstance) Primary { UnaryExpression $1 $2 $3 }
| IncOrDecExpression { IncOrDecExpression_Expression $1 }
| "(" OperatorAssignment ")" { OperatorAssignment_Expression $2 }
| Expression BinaryOperator many(AttributeInstance) Expression { BinaryExpression $1 $2 $3 $4 }
| ConditionalExpression { ConditionalExpression_Expression $1 }
| InsideExpression { InsideExpression_Expression $1 }
| TaggedUnionExpression { TaggedUnionExpression_Expression $1 }


TaggedUnionExpression :: { TaggedUnionExpression }
: "tagged" MemberIdentifier opt(Expression)
  { TaggedUnionExpression $2 $3 }

InsideExpression :: { InsideExpression }
: Expression "inside" "[" OpenRangeList "]"
  { InsideExpression $1 $4 }


ValueRange :: { ValueRange }
: Expression { Left $1 }
| "[" Expression ":" Expression "]" { Right ($2, $4) }


MintypmaxExpression :: { MintypmaxExpression }
: Expression ":" Expression ":" Expression { Right ($1, $3, $5) }
| Expression { Left $1 }


PartSelectRange :: { PartSelectRange }
: ConstantRange { Left $1 }
| IndexedRange { Right $1 }

IndexedRange :: { IndexedRange }
: Expression "+" ":" ConstantExpression { PlusIndexedRange $1 $4 }
| Expression "-" ":" ConstantExpression { MinusIndexedRange $1 $4 }



-- | A.8.4 Primaries
--

ConstantPrimary :: { ConstantPrimary }
: PrimaryLiteral { PrimaryLiteral_ConstantPrimary $1 }
| PsParameterIdentifier ConstantSelect { PsParameterIdentifier_ConstantPrimary $1 $2 }
-- | SpecparamIdentifier opt(ConstantRangeExpression) { SpecparamIdentifier_ConstantPrimary $1 $2 }
| GenvarIdentifier { GenvarIdentifier_ConstantPrimary $1 }
| FormalPortIdentifier ConstantSelect { FormalPortIdentifier_ConstantPrimary $1 $2 }
| opt(either(PackageScope, ClassScope)) EnumIdentifier { EnumIdentifier_ConstantPrimary $1 $2 }
| ConstantConcatenation opt(between("[", "]", ConstantRangeExpression)) { ConstantConcatenation_ConstantPrimary $1 $2 }
| ConstantMultipleConcatenation opt(between("[", "]", ConstantRangeExpression)) { ConstantMultipleConcatenation_ConstantPrimary $1 $2 }
-- | ConstantFunctionCall { ConstantFunctionCall_ConstantPrimary $1 }
| ConstantLetExpression { ConstantLetExpression_ConstantPrimary $1 }
| "(" ConstantMintypmaxExpression ")" { ConstantMintypmaxExpression_ConstantPrimary $2 }
| ConstantCast { ConstantCast_ConstantPrimary $1 }
| ConstantAssignmentPatternExpression { ConstantAssignmentPatternExpression_ConstantPrimary $1 }
| TypeReference { TypeReference_ConstantPrimary $1 }



Primary :: { Primary }
: PrimaryLiteral { PrimaryLiteral_Primary $1 }
| opt(either(ClassQualifier, PackageScope)) HierarchicalIdentifier Select
  { HierarchicalIdentifier_Primary $1 $2 $3 }
| EmptyQueue { EmptyPrimary }
| Concatenation opt(between("[", "]", RangeExpression))
  { Concatenation_Primary $1 $2 }
| MultipleConcatenation opt(between("[", "]", RangeExpression))
  { MultipleConcatenation_Primary $1 $2 }
-- | FunctionSubroutineCall { FunctionSubroutineCall_Primary $1 }
| LetExpression { LetExpression_Primary $1 }
| "(" MintypmaxExpression ")" { MintypmaxExpression_Primary $2 }
| Cast { Cast_Primary $1 }
| AssignmentPatternExpression { AssignmentPatternExpression_Primary $1 }
| StreamingConcatenation { StreamingConcatenation_Primary $1 }
-- | SequenceMethodCall { SequenceMethodCall_Primary $1 }
| "this" { ThisPrimary }
| "$" { DollarPrimary }
| "null" { NullPrimary }


ClassQualifier :: { ClassQualifier }
: opt(second("local", "::")) opt(either(first(ImplicitClassHandle, "."), ClassScope))
  { ClassQualifier (() <$ $1) $2 }


RangeExpression :: { RangeExpression }
: Expression { Left $1 }
| PartSelectRange { Right $1 }


PrimaryLiteral :: { PrimaryLiteral }
: Number { Number_PrimaryLiteral $1 }
| TimeLiteral { TimeLiteral_PrimaryLiteral $1 }
| UnbasedUnsizedLiteral { UnbasedUnsizedLiteral_PrimaryLiteral $1 }
| StringLiteral { StringLiteral_PrimaryLiteral $1 }


TimeLiteral :: { TimeLiteral }
: UnsignedNumber TimeUnit { UnsignedTimeLiteral $1 $2 }
| FixedPointNumber TimeUnit { FixedPointTimeLiteral $1 $2 }

TimeUnit :: { TimeUnit }
: Identifier { $1 }


ImplicitClassHandle :: { ImplicitClassHandle }
: "this" "." "super"  { ThisSuper }
| "super" { Super }
| "this" { This }


BitSelect :: { BitSelect }
: many(between("[", "]", Expression)) { $1 }

Select :: { Select }
: opt(tuple(many(tuple(second(".", MemberIdentifier), BitSelect)), second(".", MemberIdentifier)))
  BitSelect opt(between("[", "]", PartSelectRange))
  { Select $1 $2 $3 }


ConstantBitSelect :: { ConstantBitSelect }
: many(between("[", "]", ConstantExpression)) { $1 }


ConstantSelect :: { ConstantSelect }
: opt(tuple(many(tuple(second(".", MemberIdentifier), ConstantBitSelect)), second(".", MemberIdentifier)))
  ConstantBitSelect opt(between("[", "]", ConstantPartSelectRange))
  { ConstantSelect $1 $2 $3 }



ConstantCast :: { ConstantCast }
: CastingType "'" "(" ConstantExpression ")" { ConstantCast $1 $4 }


ConstantLetExpression :: { ConstantLetExpression }
: LetExpression { $1 }


Cast :: { Cast }
: CastingType "'" "(" Expression ")"
  { Cast $1 $4 }


-- | A.8.5 Expression left-side values
--

VariableLvalue :: { VariableLvalue }
: HierarchicalVariableIdentifier Select
  { HierarchicalVariableIdentifier_VariableLvalue $1 $2 }
| "{" sepBy1(VariableLvalue, ",") "}"
  { VariableLvalues_VariableLvalue $2 }
| opt(AssignmentPatternExpressionType) AssignmentPatternVariableLvalue
  { AssignmentPatternVariableLvalue_VariableLvalue $1 $2 }
| StreamingConcatenation { StreamingConcatenation_VariableLvalue $1 }


-- | A.8.6 Operators
--

UnaryOperator :: { UnaryOperator }
: "!" { NotUn }
| "~" "&" { TildeAmpUn }
| "~" "|" { TildePipeUn }
| "^" "~" { CaretTildeUn }
| "~" "^" { TildeCaretUn }
| "&" { AmpUn }
| "|" { PipeUn }
| "~" { TildeUn }
| "^" { TildeCaretUn }


BinaryOperator :: { BinaryOperator }
: "+" { PlusBin }
| "-" { MinusBin }
| "*" { StarBin }
| "/" { SlashBin }
| "%" { PercentBin }
| "==" { EqualsBin }
| "!=" { NotEqualsBin }
| "===" { EquivalentBin }
| "!==" { NotEquivalentBin }
| "&&" { AndBin }
| "||" { OrBin }
| "&" { AmpBin }
| "|" { PipeBin }
| "^" "~" { CaretTildeBin }
| "~" "^" { TildeCaretBin }
| "^" { CaretBin }


IncOrDecOperator :: { IncOrDecOperator }
: "++" { Increment }
| "--" { Decrement }


-- | A.8.7 Numbers
--

Number :: { Number }
: IntegralNumber { IntegralNumber_Number $1 }
| RealNumber { RealNumber_Number $1 }


IntegralNumber :: { IntegralNumber }
: DecimalNumber { DecimalNumber_IntegralNumber $1 }
| OctalNumber { OctalNumber_IntegralNumber $1 }
| BinaryNumber { BinaryNumber_IntegralNumber $1 }
| HexNumber { HexNumber_IntegralNumber $1 }


DecimalNumber :: { DecimalNumber }
: UnsignedNumber { UnsignedNumber_DecimalNumber Nothing $1 }
| opt(Size) DecimalBase UnsignedNumber { UnsignedNumber_DecimalNumber $1 $3 }
| opt(Size) DecimalBase xdigit { X_DecimalNumber $1 (content $3) }
| opt(Size) DecimalBase zdigit { Z_DecimalNumber $1 (content $3) }

BinaryNumber :: { BinaryNumber }
: opt(Size) BinaryBase BinaryValue { BinaryNumber $1 $3 }

OctalNumber :: { OctalNumber }
: opt(Size) OctalBase OctalValue { OctalNumber $1 $3 }

HexNumber :: { HexNumber }
: opt(Size) HexBase HexValue { HexNumber $1 $3 }


RealNumber :: { RealNumber }
: FixedPointNumber { FixedPointNumber_RealNumber $1 }
| UnsignedNumber opt(second(".", UnsignedNumber)) "exp" opt(Sign) UnsignedNumber
  { UnsignedNumber_RealNumber $1 $2 $4 $5 }


FixedPointNumber :: { FixedPointNumber }
: UnsignedNumber "." UnsignedNumber { ($1, $3) }


Sign :: { Sign }
: "+" { Plus }
| "-" { Minus }


Size :: { Size }
: UnsignedNumber { $1 }

UnbasedUnsizedLiteral :: { UnbasedUnsizedLiteral }
: "'" UnsignedNumber { UnbasedUnsizedLiteral $2 }


UnsignedNumber :: { UnsignedNumber }
: unsignedNumber { content $1 }

BinaryValue :: { BinaryValue }
: binaryValue { content $1 }

OctalValue :: { OctalValue }
: octalValue { content $1 }

HexValue :: { HexValue }
: hexValue { content $1 }


DecimalBase :: { DecimalBase }
: decimalBase { content $1 }

BinaryBase :: { BinaryBase }
: binaryBase { content $1 }

OctalBase :: { OctalBase }
: octalBase { content $1 }

HexBase :: { HexBase }
: hexBase { content $1 }


-- | A.8.8 Strings
--

StringLiteral :: { StringLiteral }
: stringLit { content $1 }



-- | A.9 General
-- 
--   A.9.1 Attributes
--

AttributeInstance :: { AttributeInstance }
: "(" "*" sepBy1(AttrSpec, ",") "*" ")" { $3 }


AttrSpec :: { AttrSpec }
: AttrName opt(second("=", ConstantExpression)) { AttrSpec $1 $2 }


AttrName :: { AttrName }
: Identifier { $1 }


-- | A.9.3 Identifiers
--

LibraryIdentifier :: { LibraryIdentifier }
: Identifier { $1 }

ModuleIdentifier :: { LibraryIdentifier }
: Identifier { $1 }

ClassIdentifier :: { ClassIdentifier }
: Identifier { $1 }

EnumIdentifier :: { EnumIdentifier }
: Identifier { $1 }

TypeIdentifier :: { TypeIdentifier }
: Identifier { $1 }

PortIdentifier :: { PortIdentifier }
: Identifier { $1 }

FormalPortIdentifier :: { FormalPortIdentifier }
: Identifier { $1 }

GenvarIdentifier :: { GenvarIdentifier }
: Identifier { $1 }

InterfaceIdentifier :: { InterfaceIdentifier }
: Identifier { $1 }

ModportIdentifier :: { ModportIdentifier }
: Identifier { $1 }

CovergroupIdentifier :: { CovergroupIdentifier }
: Identifier { $1 }

PackageIdentifier :: { PackageIdentifier }
: Identifier { $1 }

MemberIdentifier :: { MemberIdentifier }
: Identifier { $1 }

ParameterIdentifier :: { ParameterIdentifier }
: Identifier { $1 }

MethodIdentifier :: { MethodIdentifier }
: Identifier { $1 }

NetTypeIdentifier :: { NetTypeIdentifier }
: Identifier { $1 }

LetIdentifier :: { LetIdentifier }
: Identifier { $1 }

DynamicArrayVariableIdentifier :: { DynamicArrayVariableIdentifier }
: Identifier { $1 }

ClassVariableIdentifier :: { ClassVariableIdentifier }
: Identifier { $1 }

VariableIdentifier :: { VariableIdentifier }
: Identifier { $1 }

GenerateBlockIdentifier :: { GenerateBlockIdentifier }
: Identifier { $1 }


HierarchicalIdentifier :: { HierarchicalIdentifier }
: opt(second("$root", "."))
  sepBy(tuple(Identifier, ConstantBitSelect), ".") Identifier
  { HierarchicalIdentifier (() <$ $1) $2 $3 }

HierarchicalVariableIdentifier :: { HierarchicalVariableIdentifier }
: HierarchicalIdentifier { $1 }



PackageScope :: { PackageScope }
: PackageIdentifier "::" { Just $1 }
| "unitscope" "::" { Nothing }


PsClassIdentifier :: { PsClassIdentifier }
: opt(PackageScope) ClassIdentifier { PsClassIdentifier $1 $2 }

PsCovergroupIdentifier :: { PsCovergroupIdentifier }
: opt(PackageScope) CovergroupIdentifier { PsCovergroupIdentifier $1 $2 }

PsParameterIdentifier :: { PsParameterIdentifier }
: opt(either(PackageScope, ClassScope))
  ParameterIdentifier
  { PsParameterIdentifier $1 [] $2 }
| sepBy(tuple(GenerateBlockIdentifier, opt(between("[", "]", ConstantExpression))), ".")
  ParameterIdentifier
  { PsParameterIdentifier Nothing $1 $2 }


PsTypeIdentifier :: { PsTypeIdentifier }
: "local" "::" TypeIdentifier { PsTypeIdentifier (Just Nothing) $3 }
| PackageScope TypeIdentifier { PsTypeIdentifier (Just (Just $1)) $2 }
| TypeIdentifier { PsTypeIdentifier Nothing $1 }



FilePathSpec :: { FilePathSpec }
: Identifier { $1 }



Identifier :: { Identifier }
: ident { content $1 }



-- | Higher order combinators
--

tuple(a, b)
: a b { ($1, $2) }

between(a, b, p)
: a p b { $2 }

sepBy(p, s)
: sepBy1(p, s) s p { $3 : $1 }
| { [] }

sepBy1(p, s)
: sepBy1(p, s) s p { $3 : $1 }
| p { [$1] }

many1(p)
: many(p) p { $2 : $1 }
| p { [$1] }

many(p)
: many(p) p { $2 : $1 }
| { [] }

opt(p)
: p { Just $1 }
|   { Nothing }

either(l, r)
: l { Left  $1 }
| r { Right $1 }

first(p, a)
: p a { $1 }

second(a, p)
: a p { $2 }

third(a, b, p)
: a b p { $3 }


{

content :: Lexer Token -> Text
content (L _ t) = t ^. parsed

parseError :: [Lexer Token] -> a
parseError a = case a of
  [] -> error "Parse error: no tokens left to parse."
  L (l, c) t : _ -> error $ unwords ["Parse error:", "line", show l, "column", show c, "token", show t]

}
