{
module Language.SystemVerilog.Parser where

import Data.Bits
import Data.List
import qualified Data.Text as T

import Language.SystemVerilog.Syntax
import Language.SystemVerilog.Tokens
}

%name ast
%tokentype { Token }
%error { parseError }

%token

ident  { Tok_Ident _ }
xdigit { Tok_XDigit _ }
zdigit { Tok_XDigit _ }

unsignedNumber { Tok_UnsignedNumber _ }
binaryValue { Tok_BinaryValue _ }
octalValue { Tok_OctalValue _ }
hexValue { Tok_HexValue _ }

decimalBase { Tok_DecimalBase _ }
binaryBase { Tok_BinaryBase _ }
octalBase { Tok_OctalBase _ }
hexBase { Tok_HexBase _ }

stringLit { Tok_StrinLit _ }


"1step" { Tok_1step }
"accepton" { Tok_Accepton }
"alias" { Tok_Alias }
"always" { Tok_Always }
"alwayscomb" { Tok_Alwayscomb }
"alwaysff" { Tok_Alwaysff }
"alwayslatch" { Tok_Alwayslatch }
"&" { Tok_Amp }
"and" { Tok_And }
"&&" { Tok_Andop }
"'" { Tok_Apos }
"arrow" { Tok_Arrow }
"asscaret" { Tok_Asscaret }
"assert" { Tok_Assert }
"assign" { Tok_Assign }
"=" { Tok_Assignop }
"assminus" { Tok_Assminus }
"asspercent" { Tok_Asspercent }
"asspipe" { Tok_Asspipe }
"assplus" { Tok_Assplus }
"assshiftl" { Tok_Assshiftl }
"assshiftll" { Tok_Assshiftll }
"assshiftr" { Tok_Assshiftr }
"assshiftrr" { Tok_Assshiftrr }
"assslash" { Tok_Assslash }
"ass*" { Tok_Ass* }
"assume" { Tok_Assume }
"at" { Tok_At }
"automatic" { Tok_Automatic }
"begin" { Tok_Begin }
"bind" { Tok_Bind }
"bins" { Tok_Bins }
"binsof" { Tok_Binsof }
"bit" { Tok_Bit }
"break" { Tok_Break }
"buf" { Tok_Buf }
"bufif0" { Tok_Bufif0 }
"bufif1" { Tok_Bufif1 }
"byte" { Tok_Byte }
"^" { Tok_Caret }
"case" { Tok_Case }
"casex" { Tok_Casex }
"casez" { Tok_Casez }
"cell" { Tok_Cell }
"chandle" { Tok_Chandle }
"checker" { Tok_Checker }
"class" { Tok_Class }
"clocking" { Tok_Clocking }
"cmos" { Tok_Cmos }
":" { Tok_Colon }
"," { Tok_Comma }
"config" { Tok_Config }
"const" { Tok_Const }
"constraint" { Tok_Constraint }
"context" { Tok_Context }
"continue" { Tok_Continue }
"cover" { Tok_Cover }
"covergroup" { Tok_Covergroup }
"coverpoint" { Tok_Coverpoint }
"cross" { Tok_Cross }
"deassign" { Tok_Deassign }
"--" { Tok_Decrement }
"default" { Tok_Default }
"defparam" { Tok_Defparam }
"design" { Tok_Design }
"disable" { Tok_Disable }
"dist" { Tok_Dist }
"do" { Tok_Do }
"$" { Tok_Dollar }
"." { Tok_Dot }
"doublearrow" { Tok_Doublearrow }
"doubleat" { Tok_Doubleat }
"doublehash" { Tok_Doublehash }
"double*" { Tok_Double* }
"dweq" { Tok_Dweq }
"dwne" { Tok_Dwne }
"edge" { Tok_Edge }
"else" { Tok_Else }
"end" { Tok_End }
"endcase" { Tok_Endcase }
"endchecker" { Tok_Endchecker }
"endclass" { Tok_Endclass }
"endconfig" { Tok_Endconfig }
"endfunction" { Tok_Endfunction }
"endgenerate" { Tok_Endgenerate }
"endgroup" { Tok_Endgroup }
"endinterface" { Tok_Endinterface }
"endmodule" { Tok_Endmodule }
"endpackage" { Tok_Endpackage }
"endprimitive" { Tok_Endprimitive }
"endprogram" { Tok_Endprogram }
"endproperty" { Tok_Endproperty }
"endsequence" { Tok_Endsequence }
"endtable" { Tok_Endtable }
"endtask" { Tok_Endtask }
"enum" { Tok_Enum }
"==" { Tok_Eq }
"=>" { Tok_Eqarrow }
"===" { Tok_Equivalent }
"event" { Tok_Event }
"eventually" { Tok_Eventually }
"exp" { Tok_Exp }
"expect" { Tok_Expect }
"export" { Tok_Export }
"extends" { Tok_Extends }
"extern" { Tok_Extern }
"final" { Tok_Final }
"firstmatch" { Tok_Firstmatch }
"followedby" { Tok_Followedby }
"followedbyoverlapped" { Tok_Followedbyoverlapped }
"for" { Tok_For }
"force" { Tok_Force }
"foreach" { Tok_Foreach }
"forever" { Tok_Forever }
"fork" { Tok_Fork }
"function" { Tok_Function }
"generate" { Tok_Generate }
"genvar" { Tok_Genvar }
"gt" { Tok_Gt }
"gteq" { Tok_Gteq }
">>" { Tok_Gtgt }
"#" { Tok_Hash }
"highz0" { Tok_Highz0 }
"highz1" { Tok_Highz1 }
"if" { Tok_If }
"iff" { Tok_Iff }
"ifnone" { Tok_Ifnone }
"ignorebins" { Tok_Ignorebins }
"illegalbins" { Tok_Illegalbins }
"implements" { Tok_Implements }
"implication" { Tok_Implication }
"implicationoverlapped" { Tok_Implicationoverlapped }
"implies" { Tok_Implies }
"import" { Tok_Import }
"incdir" { Tok_Incdir }
"include" { Tok_Include }
"++" { Tok_Increment }
"initial" { Tok_Initial }
"inout" { Tok_Inout }
"input" { Tok_Input }
"inside" { Tok_Inside }
"instance" { Tok_Instance }
"int" { Tok_Int }
"integer" { Tok_Integer }
"interconnect" { Tok_Interconnect }
"interface" { Tok_Interface }
"intersect" { Tok_Intersect }
"join" { Tok_Join }
"joinany" { Tok_Joinany }
"joinnone" { Tok_Joinnone }
"large" { Tok_Large }
"{" { Tok_Lbrace }
"[" { Tok_Lbracket }
"let" { Tok_Let }
"liblist" { Tok_Liblist }
"library" { Tok_Library }
"local" { Tok_Local }
"localparam" { Tok_Localparam }
"logic" { Tok_Logic }
"longint" { Tok_Longint }
"(" { Tok_Lparen }
"lt" { Tok_Lt }
"lteq" { Tok_Lteq }
"<<" { Tok_Ltlt }
"macromodule" { Tok_Macromodule }
"matches" { Tok_Matches }
"medium" { Tok_Medium }
"-" { Tok_Minus }
"modport" { Tok_Modport }
"module" { Tok_Module }
"::" { Tok_Namequal }
"nand" { Tok_Nand }
"negedge" { Tok_Negedge }
"nettype" { Tok_Nettype }
"new" { Tok_New }
"nexttime" { Tok_Nexttime }
"nmos" { Tok_Nmos }
"nor" { Tok_Nor }
"noshowcancelled" { Tok_Noshowcancelled }
"not" { Tok_Not }
"!=" { Tok_Noteq }
"!==" { Tok_Notequivalent }
"notif0" { Tok_Notif0 }
"notif1" { Tok_Notif1 }
"!" { Tok_Notop }
"null" { Tok_Null }
"option" { Tok_Option }
"or" { Tok_Or }
"||" { Tok_Orop }
"output" { Tok_Output }
"package" { Tok_Package }
"packed" { Tok_Packed }
"parameter" { Tok_Parameter }
"pathpulse" { Tok_Pathpulse }
"%" { Tok_Percent }
"|" { Tok_Pipe }
"+" { Tok_Plus }
"pmos" { Tok_Pmos }
"posedge" { Tok_Posedge }
"primitive" { Tok_Primitive }
"priority" { Tok_Priority }
"program" { Tok_Program }
"property" { Tok_Property }
"protected" { Tok_Protected }
"pull0" { Tok_Pull0 }
"pull1" { Tok_Pull1 }
"pulldown" { Tok_Pulldown }
"pullup" { Tok_Pullup }
"pulsestyleondetect" { Tok_Pulsestyleondetect }
"pulsestyleonevent" { Tok_Pulsestyleonevent }
"pure" { Tok_Pure }
"?" { Tok_Question }
"rand" { Tok_Rand }
"randc" { Tok_Randc }
"randcase" { Tok_Randcase }
"randomize" { Tok_Randomize }
"randsequence" { Tok_Randsequence }
"}" { Tok_Rbrace }
"]" { Tok_Rbracket }
"rcmos" { Tok_Rcmos }
"real" { Tok_Real }
"realtime" { Tok_Realtime }
"ref" { Tok_Ref }
"reg" { Tok_Reg }
"rejecton" { Tok_Rejecton }
"release" { Tok_Release }
"repeat" { Tok_Repeat }
"restrict" { Tok_Restrict }
"rnmos" { Tok_Rnmos }
"$root" { Tok_Rootscope }
")" { Tok_Rparen }
"rpmos" { Tok_Rpmos }
"rtran" { Tok_Rtran }
"rtranif0" { Tok_Rtranif0 }
"rtranif1" { Tok_Rtranif1 }
"salways" { Tok_Salways }
"sample" { Tok_Sample }
"scalared" { Tok_Scalared }
";" { Tok_Semi }
"sequence" { Tok_Sequence }
"seventually" { Tok_Seventually }
"shortint" { Tok_Shortint }
"shortreal" { Tok_Shortreal }
"showcancelled" { Tok_Showcancelled }
"signed" { Tok_Signed }
"/" { Tok_Slash }
"small" { Tok_Small }
"snexttime" { Tok_Snexttime }
"soft" { Tok_Soft }
"solve" { Tok_Solve }
"specify" { Tok_Specify }
"specparam" { Tok_Specparam }
"*" { Tok_Star }
"static" { Tok_Static }
"std" { Tok_Std }
"string" { Tok_String }
"strong" { Tok_Strong }
"strong0" { Tok_Strong0 }
"strong1" { Tok_Strong1 }
"struct" { Tok_Struct }
"suntil" { Tok_Suntil }
"suntilwith" { Tok_Suntilwith }
"super" { Tok_Super }
"supply0" { Tok_Supply0 }
"supply1" { Tok_Supply1 }
"syncrejecton" { Tok_Syncrejecton }
"table" { Tok_Table }
"tagged" { Tok_Tagged }
"task" { Tok_Task }
"tffullskew" { Tok_Tffullskew }
"tfhold" { Tok_Tfhold }
"tfnochange" { Tok_Tfnochange }
"tfperiod" { Tok_Tfperiod }
"tfrecovery" { Tok_Tfrecovery }
"tfrecrem" { Tok_Tfrecrem }
"tfremoval" { Tok_Tfremoval }
"tfsetup" { Tok_Tfsetup }
"tfsetuphold" { Tok_Tfsetuphold }
"tfskew" { Tok_Tfskew }
"tftimeskew" { Tok_Tftimeskew }
"this" { Tok_This }
"throughout" { Tok_Throughout }
"~" { Tok_Tilde }
"time" { Tok_Time }
"timeprecision" { Tok_Timeprecision }
"timeunit" { Tok_Timeunit }
"tran" { Tok_Tran }
"tranif0" { Tok_Tranif0 }
"tranif1" { Tok_Tranif1 }
"tri" { Tok_Tri }
"tri0" { Tok_Tri0 }
"tri1" { Tok_Tri1 }
"triand" { Tok_Triand }
"trior" { Tok_Trior }
"&&&" { Tok_Tripleamp }
"trireg" { Tok_Trireg }
"type" { Tok_Type }
"typedef" { Tok_Typedef }
"typeoption" { Tok_Typeoption }
"union" { Tok_Union }
"unique" { Tok_Unique }
"unique0" { Tok_Unique0 }
"unitscope" { Tok_Unitscope }
"unsigned" { Tok_Unsigned }
"until" { Tok_Until }
"untilwith" { Tok_Untilwith }
"untyped" { Tok_Untyped }
"use" { Tok_Use }
"uwire" { Tok_Uwire }
"var" { Tok_Var }
"vectored" { Tok_Vectored }
"virtual" { Tok_Virtual }
"void" { Tok_Void }
"wait" { Tok_Wait }
"waitorder" { Tok_Waitorder }
"wand" { Tok_Wand }
"weak" { Tok_Weak }
"weak0" { Tok_Weak0 }
"weak1" { Tok_Weak1 }
"while" { Tok_While }
"wildcard" { Tok_Wildcard }
"wire" { Tok_Wire }
"with" { Tok_With }
"within" { Tok_Within }
"wor" { Tok_Wor }
"xnor" { Tok_Xnor }
"xor" { Tok_Xor }

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
  { ModuleNonAnsiHeader $1 $2 $3 $4 $5 $6 $7 }


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
  ModuleKeyword opt(Lifetime) "(" "." "*" ")" ";"
  opt(TimeunitsDeclaration)
  many(ModuleItem)
  "endmodule"
  opt(second(":", ModuleIdentifier))
  { ModuleDeclaration $1 $2 $3 $4 $9 $10 $12 }
| "extern" ModuleNonAnsiHeader { ExternModuleNonAnsiHeader_ModuleDeclaration }
| "extern" ModuleAnsiHeader { ExternModuleAnsiHeader_ModuleDeclaration }


ModuleKeyword :: { ModuleKeyword }
: "module" { Module }
| "macromodule" { Macromodule }


TimeunitsDeclaration :: { TimeunitsDeclaration }
: "timeunit" TimeLiteral opt(between("/", ";", TimeLiteral))
  { TimeunitsDeclaration (Just $2) $3 }
| "timeprecision" TimeLiteral ";"
  { TimeunitsDeclaration Nothing $2 }
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
| DataType ListOfParamAssignments { DataType_ParameterPortDeclaration $1 }
| "type" ListOfTypeAssignments { TypeAssignments_ParameterPortDeclaration $2 }


ListOfPorts :: { [Port] }
: "(" sepBy1(Port, ",") ")" { $2 }


ListOfPortDeclarations :: { ListOfPortDeclarations }
: "(" opt(sepBy1(tuple(many(AttributeInstance), AnsiPortDeclaration), ",")) ")"
  { $2 }


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
  { InterfacePortHeader $1 $2 }


AnsiPortDeclaration :: { AnsiPortDeclaration }
: opt(NetPortHeader) PortIdentifier many(UnpackedDimension) opt(second("=", ConstantExpression))
  { NetPortHeader_AnsiPortDeclaration $1 $2 $3 $4 }
| opt(InterfacePortHeader) PortIdentifier many(UnpackedDimension) opt(second("=", ConstantExpression))
  { InterfacePortHeader_AnsiPortDeclaration $1 $2 $3 $4 }
| opt(VariablePortHeader) PortIdentifier many(UnpackedDimension) opt(second("=", ConstantExpression))
  { VariablePortHeader_AnsiPortDeclaration $1 $2 $3 $4 }
| opt(PortDirection) "." PortIdentifier "(" opt(Expression) ")"
  { AnsiPortDeclaration $1 $3 $5 }


-- | A.1.4 Module items
--

ModuleItem :: { ModuleItem }
: PortDeclaration ";" { PortDeclaration_ModuleItem $1 }
| NonPortModuleItem { NonPortModuleItem_ModuleItem $1 }


NonPortModuleItem :: { NonPortModuleItem }
: GenerateRegion { GenerateRegion_NonPortModuleItem $1 }
| ModuleOrGenerateItem { ModuleOrGenerateItem_NonPortModuleItem $1 }
| SpecifyBlock { SpecifyBlock_NonPortModuleItem $1 }
-- | SpecparamDeclaration { SpecparamDeclaration_NonPortModuleItem $1 }
-- | ProgramDeclaration { ProgramDeclaration_NonPortModuleItem $1 }
| ModuleDeclaration { ModuleDeclaration_NonPortModuleItem $1 }
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
  { Interface_DataType $2 $3 $4 $5 }
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
| "union" opt("tagged")  { TUnion  }


TypeReference :: { TypeReference }
: "type" "(" Expression ")" { Expression_TypeReference $3 }
| "type" "(" DataType ")" { DataType_TypeReference $3 }



-- | A.2.3 Declaration lists
--

ListOfParamAssignments :: { ListOfParamAssignments }
: sepBy1(ParamAssignment, ",") { $1 }

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



-- | A.2.10 Assertion declarations
--


SequenceMethodCall :: { SequenceMethodCall }
: SequenceInstance "." MethodIdentifier { SequenceMethodCall $1 $3 }


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

AssignmentPattern :: { AssignmentPattern }
: "'" "{" sepBy1(Expression, ",") "}"
  { ExpressionList_AssignmentPattern $3 }
| "'" "{" sepBy1(tuple(StructurePatternKey, second(":", Expression)), ",") "}"
  { ExpressionList_AssignmentPattern $3 }
| "'" "{" sepBy1(tuple(ArrayPatternKey, second(":", Expression)), ",") "}"
  { ExpressionList_AssignmentPattern $3 }
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

AssignmentPatternVariableLvalue :: { AssignmentPatternNetLvalue }
: "'" "[" sepBy1(VariableLvalue, ",") "]" { $3 }


-- | A.8 Expressions
--
--   A.8.1 Concatenations
--

Concatenation :: { Concatenation }
: "{" sepBy1(Expression, ",") "}"
  { $2 }


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
  { StreamConcatenation $2 $3 $4 }


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
| Expression "+" ":" Expression { ArrayRangeP $1 $3 }
| Expression "-" ":" Expression { ArrayRangeM $1 $3 }
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
  { TernaryConstantExpression $1 $3 $4 $5 }


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


ConstantRangeExpression :: { ConstantRange }
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
| "(" ConstantMintypmaxExpression ")" { ConstantMintypmaxExpression_ConstantPrimary $1 }
| ConstantCast { ConstantCast_ConstantPrimary }
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
| SequenceMethodCall { SequenceMethodCall_Primary $1 }
| "this" { ThisPrimary }
| "$" { DollarPrimary }
| "null" { NullPrimary }


ClassQualifier :: { ClassQualifier }
: opt(second("local", "::")) opt(either(first(ImplicitDataType, "."), ClassScope))
  { ClassQualifier $1 $2 }


RangeExpression :: { RangeExpression }
: Expression { Left $1 }
| PartSelectRange { Right $1 }


PrimaryLiteral :: { PrimaryLiteral }
: Number { Number_PrimaryLiteral $1 }
| TimeLiteral { TimeLiteral_PrimaryLiteral $1 }
| UnbasedUnsizedLiteral { UnbasedUnsizedLiteral $1 }
| StringLiteral { StringLiteral_PrimaryLiteral $1 }


TimeLiteral :: { TimeLiteral }
: UnsignedNumber TimeUnit { UnsignedTimeLiteral $1 $2 }
| FixedPointNumber TimeUnit { FixedPointTimeLiteral $1 $2 }

TimeUnit :: { TimeUnit }
: Identifier { $1 }


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

-- | A.8.5 Expression left-side values
--

VariableLvalue :: { VariableLvalue }
: HierarchicalVariableIdentifier Select
  { HierarchicalVariableIdentifier_VariableLvalue $1 $2 }
| "{" sepBy1(VariableLvalue, ",") "}"
  { VariableLvalues_VariableLvalue $2 }
| opt(AssignmentPatternExpressionType) AssignmentPatternVariableLvalue
  { AssignmentPatternVariableLvalue_VariableLvalue $1 $2 }
| StreamingConcatenation { StreamingConcatenation_VariableLvalue }


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
| "^" { TildeCaret }


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
| opt(Size) DecimalBase xdigit { X_DecimalNumber $1 $3 }
| opt(Size) DecimalBase zdigit { Z_DecimalNumber $1 $3 }

BinaryNumber :: { BinaryNumber }
: opt(Size) BinaryBase BinaryValue { BinaryNumber $1 $3 }

OctalNumber :: { OctalNumber }
: opt(Size) OctalBase OctalValue { OctalNumber $1 $3 }

HexNumber :: { HexNumber }
: opt(Size) HexBase HexValue { HexNumber $1 $3 }


RealNumber :: { RealNumber }
: FixedPointNumber { FixedPointNumber_RealNumber $1 }
| UnsignedNumber opt(second(".", UnsignedNumber)) "exp" opt(Sign) UnsignedNumber
  { UnsignedNumber_RealNumber $1 $2 $3 $4 }


FixedPointNumber :: { FixedPointNumber }
: UnsignedNumber "." UnsignedNumber { ($1, $3) }


Sign :: { Sign }
: "+" { Plus }
| "-" { Minus }


Size :: { Size }
: UnsignedNumber { $1 }

UnbasedUnsizedLiteral :: { UnbasedUnsizedLiteral }
: "'" UnsignedNumber { $2 }


UnsignedNumber :: { UnsignedNumber }
: unsignedNumber { fromUnsignedNumber($1) }

BinaryValue :: { BinaryValue }
: binaryValue { fromBinaryValue($1) }

OctalValue :: { OctalValue }
: octalValue { fromOctalValue($1) }

HexValue :: { HexValue }
: hexValue { fromHexValue($1) }


DecimalBase :: { DecimalBase }
: decimalBase { $1 }

BinaryBase :: { BinaryBase }
: binaryBase { $1 }

OctalBase :: { OctalBase }
: octalBase { $1 }

HexBase :: { HexBase }
: hexBase { $1 }


-- | A.8.8 Strings
--

StringLiteral :: { StringLiteral }
: stringLit { stringLiteral $1 }



-- | A.9 General
-- 
--   A.9.1 Attributes
--

AttributeInstance :: { AttributeInstance }
: "(" "*" sepBy1(AttrSpec, ",") "*" ")" { AttributeInstance $3 }


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
  { HierarchicalIdentifier $1 $2 $3 }

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
| PackageScope TypeIdentifier { PsTypeIdentifier (Just $1) $2 }
| TypeIdentifier { PsTypeIdentifier Nothing }



FilePathSpec :: { FilePathSpec }
: Identifier { $1 }



Identifier :: { Identifier }
: ident { identifier $1 }



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

identifier :: Token -> Identifier
identifier (Tok_Ident s) = s
identifier _ = mempty

stringLiteral :: Token -> Identifier
stringLiteral (Tok_StringLit s) = s
stringLiteral _ = mempty


parseError :: [Token] -> a
parseError a = case a of
  []              -> error "Parse error: no tokens left to parse."
}
