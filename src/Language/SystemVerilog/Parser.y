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

"1step" { Tok_1step }
"accepton" { Tok_Accepton }
"alias" { Tok_Alias }
"always" { Tok_Always }
"alwayscomb" { Tok_Alwayscomb }
"alwaysff" { Tok_Alwaysff }
"alwayslatch" { Tok_Alwayslatch }
"amp" { Tok_Amp }
"and" { Tok_And }
"andop" { Tok_Andop }
"apos" { Tok_Apos }
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
"caret" { Tok_Caret }
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
"decrement" { Tok_Decrement }
"default" { Tok_Default }
"defparam" { Tok_Defparam }
"design" { Tok_Design }
"disable" { Tok_Disable }
"dist" { Tok_Dist }
"do" { Tok_Do }
"dollar" { Tok_Dollar }
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
"eq" { Tok_Eq }
"eqarrow" { Tok_Eqarrow }
"equivalent" { Tok_Equivalent }
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
"gtgt" { Tok_Gtgt }
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
"increment" { Tok_Increment }
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
"lbrace" { Tok_Lbrace }
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
"ltlt" { Tok_Ltlt }
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
"noteq" { Tok_Noteq }
"notequivalent" { Tok_Notequivalent }
"notif0" { Tok_Notif0 }
"notif1" { Tok_Notif1 }
"notop" { Tok_Notop }
"null" { Tok_Null }
"option" { Tok_Option }
"or" { Tok_Or }
"orop" { Tok_Orop }
"output" { Tok_Output }
"package" { Tok_Package }
"packed" { Tok_Packed }
"parameter" { Tok_Parameter }
"pathpulse" { Tok_Pathpulse }
"percent" { Tok_Percent }
"pipe" { Tok_Pipe }
"plus" { Tok_Plus }
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
"question" { Tok_Question }
"rand" { Tok_Rand }
"randc" { Tok_Randc }
"randcase" { Tok_Randcase }
"randomize" { Tok_Randomize }
"randsequence" { Tok_Randsequence }
"rbrace" { Tok_Rbrace }
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
"rootscope" { Tok_Rootscope }
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
"slash" { Tok_Slash }
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
"tilde" { Tok_Tilde }
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
"tripleamp" { Tok_Tripleamp }
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


-- | A.2.2 Declaration types
--
--   A.2.2.1 Net and variable types
--

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
: "struct"             { TStruct }
| "union" opt(Tagged)  { TUnion  }


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



-- | A.8.3 Expressions
--





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

EnumIdentifier :: { EnumIdentifier }
: Identifier { $1 }

TypeIdentifier :: { TypeIdentifier }
: Identifier { $1 }

InterfaceIdentifier :: { IntefaceIdentifier }
: Identifier { $1 }

CovergroupIdentifier :: { CovergroupIdentifier }
: Identifier { $1 }


PsClassIdentifier :: { PsClassIdentifier }
: opt(PackageScope) ClassIdentifier { PsClassIdentifier $1 $2 }

PsCovergroupIdentifier :: { PsCovergroupIdentifier }
: opt(PackageScope) CovergroupIdentifier { PsCovergroupIdentifier $1 $2 }


FilePathSpec :: { FilePathSpec }
: Identifier { $1 }



Identifier :: { Identifier }
: { mempty }



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

second(a, p)
: a p { $2 }

third(a, b, p)
: a b p { $3 }


{
parseError :: [Token] -> a
parseError a = case a of
  []              -> error "Parse error: no tokens left to parse."
}
