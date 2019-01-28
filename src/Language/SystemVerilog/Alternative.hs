{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Language.SystemVerilog.Alternative where

import Control.Applicative ((<|>))
import Data.Char
import Data.Text (Text)
import Prelude hiding ((>>))

import Language.SystemVerilog.Alternative.Grammar

parseAST :: Text -> Either ParseError [AST]
parseAST = runResult . runParser (many1 ast) mempty . lexer mempty

ast :: Parser AST
ast
  =   LibraryText_AST <$> libraryText
  <|> SourceText_AST <$> sourceText
  <?> "ast"


-- | A.1 Source text
--
--  A.1.1 Library source text
--

libraryText :: Parser LibraryText
libraryText = LibraryText
  <$> many1 libraryDescription
  <?> "library_text"

libraryDescription :: Parser LibraryDescription
libraryDescription
  =   LibraryDeclaration_LibraryDescription <$> libraryDeclaration
  <|> IncludeStatement_LibraryDescription <$> includeStatement
  <|> ConfigDeclaration_LibraryDescription <$> configDeclaration
  <|> NoLibraryDescription <$ semi
  <?> "library_description"

libraryDeclaration :: Parser LibraryDeclaration
libraryDeclaration = LibraryDeclaration
  <$> (library *> libraryIdentifier)
  <*> sepBy1 filePathSpec comma
  <*> optional (minus *> incdir *> sepBy1 filePathSpec comma)
  <*  semi
  <?> "library_declaration"

includeStatement :: Parser IncludeStatement
includeStatement = IncludeStatement
  <$> (include *> filePathSpec)
  <*  semi
  <?> "include_statement"


-- | A.1.2 SystemVerilog source text
--
sourceText :: Parser SourceText
sourceText = SourceText
  <$> optional timeunitsDeclaration
  <*> many1 description
  <?> "source_text"

description :: Parser Description
description
  =   ModuleDeclaration_Description <$> moduleDeclaration
  <|> UdpDeclaration_Description <$> udpDeclaration
  <|> InterfaceDeclaration_Description <$> interfaceDeclaration
  <|> ProgramDeclaration_Description <$> programDeclaration
  <|> PackageDeclaration_Description <$> packageDeclaration
  <|> PackageItem_Description <$> many attributeInstance <*> packageItem
  <|> BindDirective_Description <$> many attributeInstance <*> bindDirective
  <|> ConfigDeclaration_Description <$> configDeclaration
  <?> "description"

moduleNonAnsiHeader :: Parser ModuleNonAnsiHeader
moduleNonAnsiHeader = ModuleNonAnsiHeader
  <$> many attributeInstance
  <*> moduleKeyword
  <*> optional lifetime
  <*> moduleIdentifier
  <*> many packageImportDeclaration
  <*> optional parameterPortList
  <*> (listOfPorts <* semi)
  <?> "module_non_ansi_header"
  
moduleAnsiHeader :: Parser ModuleAnsiHeader
moduleAnsiHeader = ModuleAnsiHeader
  <$> many attributeInstance
  <*> moduleKeyword
  <*> optional lifetime
  <*> moduleIdentifier
  <*> many packageImportDeclaration
  <*> optional parameterPortList
  <*> (optional listOfPortDeclarations <* semi)
  <?> "module_ansi_header"

moduleDeclaration :: Parser ModuleDeclaration
moduleDeclaration
  =   ModuleNonAnsiHeader_ModuleDeclaration
      <$> moduleNonAnsiHeader
      <*> optional timeunitsDeclaration
      <*> (many moduleItem <* endmodule)
      <*> optional (colon *> moduleIdentifier)
  <|> ModuleAnsiHeader_ModuleDeclaration
      <$> moduleAnsiHeader
      <*> optional timeunitsDeclaration
      <*> (many nonPortModuleItem <* endmodule)
      <*> optional (colon *> moduleIdentifier)
  <|> ModuleDeclaration
      <$> many attributeInstance
      <*> moduleKeyword
      <*> optional lifetime
      <*> (moduleIdentifier <* lparen <* dot <* star <* rparen <* semi)
      <*> optional timeunitsDeclaration
      <*> (many moduleItem <* endmodule)
      <*> optional (colon *> moduleIdentifier)
  <|> ExternModuleNonAnsiHeader_ModuleDeclaration
      <$> (extern *> moduleNonAnsiHeader)
  <|> ExternModuleAnsiHeader_ModuleDeclaration
      <$> (extern *> moduleAnsiHeader)
  <?> "module_declaration" 

moduleKeyword :: Parser ModuleKeyword
moduleKeyword
  =   Module <$ module_
  <|> Macromodule <$ macromodule
  <?> "module_keyword"

interfaceDeclaration :: Parser InterfaceDeclaration
interfaceDeclaration 
  =   InterfaceNonAnsiHeader_InterfaceDeclaration
      <$> interfaceNonAnsiHeader
      <*> optional timeunitsDeclaration
      <*> (many interfaceItem <* endinterface)
      <*> optional (colon *> interfaceIdentifier)
  <|> InterfaceAnsiHeader_InterfaceDeclaration
      <$> interfaceAnsiHeader
      <*> optional timeunitsDeclaration
      <*> (many nonPortInterfaceItem <* endinterface)
      <*> optional (colon *> interfaceIdentifier)
  <|> InterfaceDeclaration
      <$> many attributeInstance
      <*> (interface *> interfaceIdentifier <* lparen <* dot <* star <* rparen <* semi)
      <*> optional timeunitsDeclaration
      <*> (many interfaceItem <* endinterface)
      <*> optional (colon *> interfaceIdentifier)
  <|> ExternInterfaceNonAnsiHeader_InterfaceDeclaration
      <$> (extern *> interfaceNonAnsiHeader)
  <|> ExternInterfaceAnsiHeader_InterfaceDeclaration
      <$> (extern *> interfaceAnsiHeader)
  <?> "interface_declaration" 

interfaceNonAnsiHeader :: Parser InterfaceNonAnsiHeader
interfaceNonAnsiHeader = InterfaceNonAnsiHeader
  <$> (many attributeInstance <* interface)
  <*> optional lifetime
  <*> interfaceIdentifier
  <*> many packageImportDeclaration
  <*> optional parameterPortList
  <*> (listOfPorts <* semi)
  <?> "interface_non_ansi_header"
  
interfaceAnsiHeader :: Parser InterfaceAnsiHeader
interfaceAnsiHeader = InterfaceAnsiHeader
  <$> (many attributeInstance <* interface)
  <*> optional lifetime
  <*> interfaceIdentifier
  <*> many packageImportDeclaration
  <*> optional parameterPortList
  <*> (optional listOfPortDeclarations <* semi)
  <?> "interface_ansi_header"


programDeclaration :: Parser ProgramDeclaration
programDeclaration 
  =   ProgramNonAnsiHeader_ProgramDeclaration
      <$> programNonAnsiHeader
      <*> optional timeunitsDeclaration
      <*> (many programItem <* endprogram)
      <*> optional (colon *> programIdentifier)
  <|> ProgramAnsiHeader_ProgramDeclaration
      <$> programAnsiHeader
      <*> optional timeunitsDeclaration
      <*> (many nonPortProgramItem <* endprogram)
      <*> optional (colon *> programIdentifier)
  <|> ProgramDeclaration
      <$> many attributeInstance
      <*> (program *> programIdentifier <* lparen <* dot <* star <* rparen <* semi)
      <*> optional timeunitsDeclaration
      <*> (many programItem <* endprogram)
      <*> optional (colon *> programIdentifier)
  <|> ExternProgramNonAnsiHeader_ProgramDeclaration
      <$> (extern *> programNonAnsiHeader)
  <|> ExternProgramAnsiHeader_ProgramDeclaration
      <$> (extern *> programAnsiHeader)
  <?> "program_declaration" 

programNonAnsiHeader :: Parser ProgramNonAnsiHeader
programNonAnsiHeader = ProgramNonAnsiHeader
  <$> (many attributeInstance <* program)
  <*> optional lifetime
  <*> programIdentifier
  <*> many packageImportDeclaration
  <*> optional parameterPortList
  <*> (listOfPorts <* semi)
  <?> "program_non_ansi_header"
  
programAnsiHeader :: Parser ProgramAnsiHeader
programAnsiHeader = ProgramAnsiHeader
  <$> (many attributeInstance <* program)
  <*> optional lifetime
  <*> programIdentifier
  <*> many packageImportDeclaration
  <*> optional parameterPortList
  <*> (optional listOfPortDeclarations <* semi)
  <?> "program_ansi_header"

checkerDeclaration :: Parser CheckerDeclaration
checkerDeclaration = CheckerDeclaration
  <$> (checker *> checkerIdentifier)
  <*> (optional (lparen *> optional checkerPortList <* rparen) <* semi)
  <*> (many ((,) <$> many attributeInstance <*> checkerOrGenerateItem) <* endchecker)
  <*> optional (colon *> checkerIdentifier)
  <?> "checker_declaration"

classDeclaration :: Parser ClassDeclaration
classDeclaration = ClassDeclaration
  <$> (optional virtual_ <* class_)
  <*> optional lifetime
  <*> classIdentifier
  <*> optional parameterPortList
  <*> optional
      ((,) <$> (extends *> classType) <*> optional (between lparen rparen listOfArguments))
  <*> (optional (implements *> sepBy1 interfaceClassType comma) <* semi)
  <*> (many classItem <* endclass)
  <*> optional (colon *> classIdentifier)
  <?> "class_declaration"

interfaceClassType :: Parser InterfaceClassType
interfaceClassType = InterfaceClassType
  <$> psClassIdentifier
  <*> optional parameterValueAssignment
  <?> "interface_class_type"

interfaceClassDeclaration :: Parser InterfaceClassDeclaration
interfaceClassDeclaration = InterfaceClassDeclaration
  <$> (interface *> class_ *> classIdentifier)
  <*> optional parameterPortList
  <*> (optional (extends *> sepBy1 interfaceClassType comma) <* semi)
  <*> (many interfaceClassItem <* endclass)
  <*> optional (colon *> classIdentifier)
  <?> "interface_class_declaration"

interfaceClassItem :: Parser InterfaceClassItem
interfaceClassItem
  =   TypeDeclaration_InterfaceClassItem
      <$> typeDeclaration
  <|> InterfaceClassMethod_InterfaceClassItem
      <$> many attributeInstance
      <*> interfaceClassMethod
  <|> LocalParameterDeclaration_InterfaceClassItem
      <$> localParameterDeclaration <* semi
  <|> ParameterDeclaration_InterfaceClassItem
      <$> parameterDeclaration <* semi
  <|> NoInterfaceClassItem <$ semi
  <?> "interface_class_item"

interfaceClassMethod :: Parser InterfaceClassMethod
interfaceClassMethod = InterfaceClassMethod
  <$> (pure_ *> virtual_ *> methodPrototype)
  <*  semi
  <?> "interface_class_method"

packageDeclaration :: Parser PackageDeclaration
packageDeclaration = PackageDeclaration
  <$> (many attributeInstance <* package)
  <*> optional lifetime
  <*> (packageIdentifier <* semi)
  <*> optional timeunitsDeclaration
  <*> (many ((,) <$> many attributeInstance <*> packageItem) <* endpackage)
  <*> optional (colon *> packageIdentifier)
  <?> "package_declaration"

timeunitsDeclaration :: Parser TimeunitsDeclaration
timeunitsDeclaration
  =   TimeunitsDeclaration
      <$> (Just <$> (timeunit *> timeLiteral))
      <*> (optional (between slash semi timeLiteral))
  <|> TimeunitsDeclaration
      <$> pure Nothing
      <*> (Just <$> between timeprecision semi timeLiteral)
  <|> TimeunitsDeclaration
      <$> (Just <$> between timeunit semi timeLiteral)
      <*> (Just <$> between timeprecision semi timeLiteral)
  <|> flip TimeunitsDeclaration
      <$> (Just <$> between timeprecision semi timeLiteral)
      <*> (Just <$> between timeunit semi timeLiteral)
  <?> "timeunits_declaration"


-- | A.1.3 Module parameters and ports
--
parameterPortList :: Parser ParameterPortList
parameterPortList = hash *> between lparen rparen
  (ParameterPortList
    <$> optional listOfParamAssignments
    <*> sepBy parameterPortDeclaration comma)
  <?> "parameter_port_list"

parameterPortDeclaration :: Parser ParameterPortDeclaration
parameterPortDeclaration
  =   ParameterDeclaration_ParameterPortDeclaration <$> parameterDeclaration
  <|> LocalParameterDeclaration_ParameterPortDeclaration <$> localParameterDeclaration
  <|> DataType_ParameterPortDeclaration <$> dataType <*> listOfParamAssignments
  <|> TypeAssignments_ParameterPortDeclaration <$> (type_ *> listOfTypeAssignments)
  <?> "parameter_port_declaration"

listOfPorts :: Parser [Port]
listOfPorts = between lparen rparen (port `sepBy1` comma)
  <?> "list_of_ports"

listOfPortDeclarations :: Parser ListOfPortDeclarations
listOfPortDeclarations = between lparen rparen (optional (item `sepBy1` comma))
  <?> "list_of_port_declarations"
  where item = (,) <$> many attributeInstance <*> ansiPortDeclaration

portDeclaration :: Parser PortDeclaration
portDeclaration
  =   InoutDeclaration_PortDeclaration
      <$> many attributeInstance
      <*> inoutDeclaration
  <|> InputDeclaration_PortDeclaration
      <$> many attributeInstance
      <*> inputDeclaration
  <|> OutputDeclaration_PortDeclaration
      <$> many attributeInstance
      <*> outputDeclaration
  <|> RefDeclaration_PortDeclaration
      <$> many attributeInstance
      <*> refDeclaration
  <|> InterfacePortDeclaration_PortDeclaration
      <$> many attributeInstance
      <*> interfacePortDeclaration
  <?> "port_declaration"

port :: Parser Port
port
  =   Port
      <$> (Just <$> (dot *> portIdentifier))
      <*> between lparen rparen (optional portExpression)
  <|> Port
      <$> pure Nothing
      <*> optional portExpression
  <?> "port"

portExpression :: Parser [PortReference]
portExpression = portReference `sepBy` comma
  <?> "port_expression"

portReference :: Parser PortReference
portReference = PortReference
  <$> portIdentifier
  <*> constantSelect
  <?> "port_reference"

portDirection :: Parser PortDirection
portDirection
  =   Inout  <$ inout
  <|> Input  <$ input
  <|> Output <$ output
  <|> Ref    <$ ref
  <?> "port_direction"

netPortHeader :: Parser NetPortHeader
netPortHeader = NetPortHeader
  <$> optional portDirection
  <*> netPortType
  <?> "net_port_header"

variablePortHeader :: Parser VariablePortHeader
variablePortHeader = VariablePortHeader
  <$> optional portDirection
  <*> variablePortType
  <?> "variable_port_header"

interfacePortHeader :: Parser InterfacePortHeader
interfacePortHeader = InterfacePortHeader
  <$> (Nothing <$ interface <|> Just <$> interfaceIdentifier)
  <*> optional (dot *> modportIdentifier)
  <?> "interface_port_header"

ansiPortDeclaration :: Parser AnsiPortDeclaration
ansiPortDeclaration
   =   NetPortHeader_AnsiPortDeclaration
       <$> optional netPortHeader
       <*> portIdentifier
       <*> many unpackedDimension
       <*> optional (assign_op *> constantExpression)
   <|> InterfacePortHeader_AnsiPortDeclaration
       <$> optional interfacePortHeader
       <*> portIdentifier
       <*> many unpackedDimension
       <*> optional (assign_op *> constantExpression)
   <|> VariablePortHeader_AnsiPortDeclaration
       <$> optional variablePortHeader
       <*> portIdentifier
       <*> many variableDimension
       <*> optional (assign_op *> constantExpression)
   <|> AnsiPortDeclaration
       <$> optional portDirection
       <*> (dot *> portIdentifier)
       <*> between lparen rparen (optional expression)
   <?> "ansi_port_declaration"


-- | A.1.4 Module items
--

elaborationSystemTask :: Parser ElaborationSystemTask
elaborationSystemTask
  =   Fatal
      <$> optional
          (between lparen rparen $ (,) <$> finishNumber <*> optional (comma *> listOfArguments))
      <*  semi
  <|> Error
      <$> optional (between lparen rparen $ optional listOfArguments)
      <*  semi
  <?> "elaboration_system_task"

-- !
finishNumber :: Parser FinishNumber
finishNumber = unsignedNumber
  <?> "finish_number"

moduleCommonItem :: Parser ModuleCommonItem
moduleCommonItem
  =   ModuleOrGenerateItemDeclaration_ModuleCommonItem <$> moduleOrGenerateItemDeclaration
  <|> InterfaceInstantiation_ModuleCommonItem <$> interfaceInstantiation
  <|> ProgramInstantiation_ModuleCommonItem <$> programInstantiation
  <|> AssertionItem_ModuleCommonItem <$> assertionItem
  <|> BindDirective_ModuleCommonItem <$> bindDirective
  <|> ContinuousAssign_ModuleCommonItem <$> continuousAssign
  <|> NetAlias_ModuleCommonItem <$> netAlias
  <|> InitialConstruct_ModuleCommonItem <$> initialConstruct
  <|> FinalConstruct_ModuleCommonItem <$> finalConstruct
  <|> AlwaysConstruct_ModuleCommonItem <$> alwaysConstruct
  <|> LoopGenerateConstruct_ModuleCommonItem <$> loopGenerateConstruct
  <|> ConditionalGenerateConstruct_ModuleCommonItem <$> conditionalGenerateConstruct
  <|> ElaborationSystemTask_ModuleCommonItem <$> elaborationSystemTask
  <?> "module_common_item"

moduleItem :: Parser ModuleItem
moduleItem
  =   PortDeclaration_ModuleItem <$> portDeclaration <* semi
  <|> NonPortModuleItem_ModuleItem <$> nonPortModuleItem
  <?> "module_item"

moduleOrGenerateItem :: Parser ModuleOrGenerateItem
moduleOrGenerateItem
  =   ParameterOverride_ModuleOrGenerateItem
      <$> many attributeInstance
      <*> parameterOverride
  <|> GateInstantiation_ModuleOrGenerateItem
      <$> many attributeInstance
      <*> gateInstantiation
  <|> UdpInstantiation_ModuleOrGenerateItem
      <$> many attributeInstance
      <*> udpInstantiation
  <|> ModuleInstantiation_ModuleOrGenerateItem
      <$> many attributeInstance
      <*> moduleInstantiation
  <|> ModuleCommonItem_ModuleOrGenerateItem
      <$> many attributeInstance
      <*> moduleCommonItem
  <?> "module_or_generate_item"


moduleOrGenerateItemDeclaration :: Parser ModuleOrGenerateItemDeclaration
moduleOrGenerateItemDeclaration
  =   PackageOrGenerateItemDeclaration_ModuleOrGenerateItemDeclaration
      <$> packageOrGenerateItemDeclaration
  <|> GenvarDeclaration_ModuleOrGenerateItemDeclaration
      <$> genvarDeclaration
  <|> ClockingDeclaration_ModuleOrGenerateItemDeclaration
      <$> clockingDeclaration
  <|> ClockingIdentifier_ModuleOrGenerateItemDeclaration
      <$> (default_ *> clocking_ *> moduleIdentifier <* semi)
  <|> DisableIff_ModuleOrGenerateItemDeclaration
      <$> (default_ *> disable *> iff *> expressionOrDist <* semi)
  <?> "module_or_generate_item_declaration"

nonPortModuleItem :: Parser NonPortModuleItem
nonPortModuleItem
  =   GenerateRegion_NonPortModuleItem
      <$> generateRegion
  <|> ModuleOrGenerateItem_NonPortModuleItem
      <$> moduleOrGenerateItem
  <|> SpecifyBlock_NonPortModuleItem
      <$> specifyBlock
  <|> SpecparamDeclaration_NonPortModuleItem
      <$> many attributeInstance
      <*> specparamDeclaration
  <|> ProgramDeclaration_NonPortModuleItem
      <$> programDeclaration
  <|> ModuleDeclaration_NonPortModuleItem
      <$> moduleDeclaration
  <|> InterfaceDeclaration_NonPortModuleItem
      <$> interfaceDeclaration
  <|> TimeunitsDeclaration_NonPortModuleItem
      <$> timeunitsDeclaration
  <?> "non_port_module_item"

parameterOverride :: Parser ParameterOverride
parameterOverride = defparam *> listOfDefparamAssignments <* semi
  <?> "parameter_override"

bindDirective :: Parser BindDirective
bindDirective
  =   BindTargetScope_BindDirective
      <$> bindTargetScope
      <*> optional bindTargetInstanceList
      <*> bindInstantiation
      <*  semi
  <|> BindTargetInstance_BindDirective
      <$> bindTargetInstance
      <*> bindInstantiation
      <*  semi
  <?> "bind_directive"

bindTargetScope :: Parser BindTargetScope
bindTargetScope
  =   ModuleIdentifier_BindTargetScope <$> moduleIdentifier
  <|> InterfaceIdentifier_BindTargetScope <$> interfaceIdentifier
  <?> "bind_target_scope"

bindTargetInstance :: Parser BindTargetInstance
bindTargetInstance = BindTargetInstance
  <$> hierarchicalIdentifier
  <*> constantBitSelect
  <?> "bind_target_instance"

bindTargetInstanceList :: Parser BindTargetInstanceList
bindTargetInstanceList = bindTargetInstance `sepBy1` comma
  <?> "bind_target_instance_list"

bindInstantiation :: Parser BindInstantiation
bindInstantiation
  =   ProgramInstantiation_BindInstantiation <$> programInstantiation
  <|> ModuleInstantiation_BindInstantiation <$> moduleInstantiation
  <|> InterfaceInstantiation_BindInstantiation <$> interfaceInstantiation
  <|> CheckerInstantiation_BindInstantiation <$> checkerInstantiation
  <?> "bind_instantiation"

-- | A.1.5 Configuration source text
--
configDeclaration :: Parser ConfigDeclaration
configDeclaration = ConfigDeclaration
  <$> (config *> configIdentifier <* semi)
  <*> sepBy localParameterDeclaration semi
  <*> designStatement
  <*> (many configRuleStatement <* endconfig)
  <*> optional (colon *> configIdentifier)
  <?> "config_declaration"

designStatement :: Parser DesignStatement
designStatement = design *> many item <* semi
  <?> "design_statement"
  where item = (,) <$> optional (libraryIdentifier <* dot) <*> cellIdentifier

configRuleStatement :: Parser ConfigRuleStatement
configRuleStatement
  =   DefaultLiblistClause_ConfigRuleStatement <$> (defaultClause *> liblistClause) <* semi
  <|> InstLiblistClause_ConfigRuleStatement <$> instClause <*> liblistClause <* semi
  <|> InstUseClause_ConfigRuleStatement <$> instClause <*> useClause <* semi
  <|> CellLiblistClause_ConfigRuleStatement <$> cellClause <*> liblistClause <* semi
  <|> CellUseClause_ConfigRuleStatement <$> cellClause <*> useClause <* semi
  <?> "config_rule_statement"

defaultClause :: Parser ()
defaultClause = default_
  <?> "default_clause"

instClause :: Parser InstClause
instClause = instance_ *> instName
  <?> "inst_clause"

instName :: Parser InstName
instName = InstName
  <$> topmoduleIdentifier
  <*> sepBy instanceIdentifier dot
  <?> "inst_name"

cellClause :: Parser CellClause
cellClause = CellClause
  <$> (cell *> optional (libraryIdentifier <* dot))
  <*> cellIdentifier
  <?> "cell_clause"

liblistClause :: Parser LiblistClause
liblistClause = liblist *> many libraryIdentifier
  <?> "liblist_clause"

useClause :: Parser UseClause
useClause
  =   UseClause 
      <$> (use *> optional (libraryIdentifier <* dot))
      <*> (Just <$> cellIdentifier)
      <*> pure []
      <*> optional (colon *> config)
  <|> UseClause 
      <$> pure Nothing
      <*> pure Nothing
      <*> sepBy1 namedParameterAssignment comma
      <*> optional (colon *> config)
  <|> UseClause 
      <$> (use *> optional (libraryIdentifier <* dot))
      <*> (Just <$> cellIdentifier)
      <*> sepBy1 namedParameterAssignment comma
      <*> optional (colon *> config)
  <?> "use_clause"

-- | A.1.6 Interface items
--
interfaceOrGenerateItem :: Parser InterfaceOrGenerateItem
interfaceOrGenerateItem
  =   ModuleCommonItem_InterfaceOrGenerateItem
      <$> many attributeInstance
      <*> moduleCommonItem
  <|> ModportDeclaration_InterfaceOrGenerateItem
      <$> many attributeInstance
      <*> modportDeclaration
  <|> ExternTfDeclaration_InterfaceOrGenerateItem
      <$> many attributeInstance
      <*> externTfDeclaration
  <?> "interface_or_generate_item"

externTfDeclaration :: Parser ExternTfDeclaration
externTfDeclaration
  =   MethodPrototype_ExternTfDeclaration <$> methodPrototype <* semi
  <|> TaskPrototype_ExternTfDeclaration <$> taskPrototype <* semi
  <?> "extern_tf_declaration"

interfaceItem :: Parser InterfaceItem
interfaceItem
  =   PortDeclaration_InterfaceItem <$> portDeclaration <* semi
  <|> NonPortInterfaceItem_InterfaceItem <$> nonPortInterfaceItem
  <?> "interface_item"

nonPortInterfaceItem :: Parser NonPortInterfaceItem
nonPortInterfaceItem
  =   GenerateRegion_NonPortInterfaceItem <$> generateRegion
  <|> InterfaceOrGenerateItem_NonPortInterfaceItem <$> interfaceOrGenerateItem 
  <|> ProgramDeclaration_NonPortInterfaceItem <$> programDeclaration 
  <|> InterfaceDeclaration_NonPortInterfaceItem <$> interfaceDeclaration
  <|> TimeunitsDeclaration_NonPortInterfaceItem <$> timeunitsDeclaration
  <?> "non_port_interface_item"

-- | A.1.7 Program items
--
programItem :: Parser ProgramItem
programItem
  =   PortDeclaration_ProgramItem <$> portDeclaration <* semi
  <|> NonPortProgramItem_ProgramItem <$> nonPortProgramItem
  <?> "program_item"

nonPortProgramItem :: Parser NonPortProgramItem
nonPortProgramItem
  =   ContinuousAssign_NonPortProgramItem
      <$> many attributeInstance
      <*> continuousAssign
  <|> ModuleOrGenerateItemDeclaration_NonPortProgramItem
      <$> many attributeInstance
      <*> moduleOrGenerateItemDeclaration
  <|> InitialConstruct_NonPortProgramItem
      <$> many attributeInstance
      <*> initialConstruct
  <|> FinalConstruct_NonPortProgramItem
      <$> many attributeInstance
      <*> finalConstruct
  <|> ConcurrentAssertionItem_NonPortProgramItem
      <$> many attributeInstance
      <*> concurrentAssertionItem
  <|> TimeunitsDeclaration_NonPortProgramItem
      <$> timeunitsDeclaration
  <|> ProgramGenerateItem_NonPortProgramItem
      <$> programGenerateItem
  <?> "non_port_program_item"

programGenerateItem :: Parser ProgramGenerateItem
programGenerateItem
  =   LoopGenerateConstruct_ProgramGenerateItem <$> loopGenerateConstruct
  <|> ConditionalGenerateConstruct_ProgramGenerateItem <$> conditionalGenerateConstruct
  <|> GenerateRegion_ProgramGenerateItem <$> generateRegion
  <|> ElaborationSystemTask_ProgramGenerateItem <$> elaborationSystemTask
  <?> "program_generate_item"

-- | A.1.8 Checker items
--
checkerPortList :: Parser CheckerPortList
checkerPortList = checkerPortItem `sepBy1` comma
  <?> "checker_port_list"

checkerPortItem :: Parser CheckerPortItem
checkerPortItem = CheckerPortItem
  <$> many attributeInstance
  <*> optional checkerPortDirection
  <*> propertyFormalType
  <*> formalPortIdentifier
  <*> many variableDimension
  <*> optional (assign_op *> propertyActualArg)
  <?> "checker_port_item"

checkerPortDirection :: Parser PortDirection
checkerPortDirection
  =   Input  <$ input
  <|> Output <$ output
  <?> "checker_port_direction"

checkerOrGenerateItem :: Parser CheckerOrGenerateItem
checkerOrGenerateItem
  =   CheckerOrGenerateItemDeclaration_CheckerOrGenerateItem
      <$> checkerOrGenerateItemDeclaration
  <|> InitialConstruct_CheckerOrGenerateItem
      <$> initialConstruct
  <|> AlwaysConstruct_CheckerOrGenerateItem
      <$> alwaysConstruct
  <|> FinalConstruct_CheckerOrGenerateItem
      <$> finalConstruct
  <|> AssertionItem_CheckerOrGenerateItem
      <$> assertionItem
  <|> ContinuousAssign_CheckerOrGenerateItem
      <$> continuousAssign
  <|> CheckerGenerateItem_CheckerOrGenerateItem
      <$> checkerGenerateItem
  <?> "checker_or_generate_item"

checkerOrGenerateItemDeclaration :: Parser CheckerOrGenerateItemDeclaration
checkerOrGenerateItemDeclaration
  =   DataDeclaration_CheckerOrGenerateItemDeclaration
      <$> optional (Rand <$ rand)
      <*> dataDeclaration
  <|> FunctionDeclaration_CheckerOrGenerateItemDeclaration
      <$> functionDeclaration
  <|> CheckerDeclaration_CheckerOrGenerateItemDeclaration
      <$> checkerDeclaration
  <|> AssertionItemDeclaration_CheckerOrGenerateItemDeclaration
      <$> assertionItemDeclaration
  <|> CovergroupDeclaration_CheckerOrGenerateItemDeclaration
      <$> covergroupDeclaration
  <|> OverloadDeclaration_CheckerOrGenerateItemDeclaration
      <$> overloadDeclaration
  <|> GenvarDeclaration_CheckerOrGenerateItemDeclaration
      <$> genvarDeclaration
  <|> ClockingDeclaration_CheckerOrGenerateItemDeclaration
      <$> clockingDeclaration
  <|> Clocking_CheckerOrGenerateItemDeclaration
      <$> (default_ *> clocking_ *> clockingIdentifier)
      <*  semi
  <|> Disable_CheckerOrGenerateItemDeclaration
      <$> (default_ *> default_ *> iff *> expressionOrDist)
      <*  semi
  <?> "checker_or_generate_item_declaration"

checkerGenerateItem :: Parser CheckerGenerateItem
checkerGenerateItem
  =   LoopGenerateConstruct_CheckerGenerateItem <$> loopGenerateConstruct
  <|> ConditionalGenerateConstruct_CheckerGenerateItem <$> conditionalGenerateConstruct
  <|> GenerateRegion_CheckerGenerateItem <$> generateRegion
  <|> ElaborationSystemTask_CheckerGenerateItem <$> elaborationSystemTask
  <?> "checker_generate_item"

-- | A.1.9 Class items
--
classItem :: Parser ClassItem
classItem
  =   ClassProperty_ClassItem
      <$> many attributeInstance
      <*> classProperty
  <|> ClassMethod_ClassItem
      <$> many attributeInstance
      <*> classMethod
  <|> ClassConstraint_ClassItem
      <$> many attributeInstance
      <*> classConstraint
  <|> ClassDeclaration_ClassItem
      <$> many attributeInstance
      <*> classDeclaration
  <|> CovergroupDeclaration_ClassItem
      <$> many attributeInstance
      <*> covergroupDeclaration
  <|> LocalParameterDeclaration_ClassItem
      <$> localParameterDeclaration
      <*  semi
  <|> ParameterDeclaration_ClassItem
      <$> parameterDeclaration
      <*  semi
  <|> NoClassItem
      <$  semi
  <?> "class_item"

classProperty :: Parser ClassProperty
classProperty
  =   DataDeclaration_ClassProperty
      <$> many propertyQualifier
      <*> dataDeclaration
  <|> ConstClassProperty
      <$> (const_ *> many classItemQualifier)
      <*> dataType
      <*> constIdentifier
      <*> optional (assign_op *> constantExpression)
      <*  semi
  <?> "class_property"

classMethod :: Parser ClassMethod
classMethod
  =   TaskDeclaration_ClassMethod
      <$> many methodQualifier
      <*> taskDeclaration
  <|> FunctionDeclaration_ClassMethod
      <$> many methodQualifier
      <*> functionDeclaration
  <|> MethodPrototype_ClassMethod
      <$> (pure_ *> virtual_ *> many classItemQualifier)
      <*> methodPrototype
      <*  semi
  <|> ExternMethodPrototype_ClassMethod
      <$> (extern *> many methodQualifier)
      <*> methodPrototype
      <*  semi
  <|> ClassConstructorDeclaration_ClassMethod
      <$> many methodQualifier
      <*> classConstructorDeclaration
  <|> ClassConstructorPrototype_ClassMethod
      <$> (extern *> many methodQualifier)
      <*> classConstructorPrototype
  <?> "class_method"

classConstructorPrototype :: Parser ClassConstructorPrototype
classConstructorPrototype = function *> new
   *> optional (between lparen rparen (optional tfPortList))
  <*  semi
  <?> "class_constructor_prototype"

classConstraint :: Parser ClassConstraint
classConstraint
  =   ConstraintPrototype_ClassConstraint <$> constraintPrototype
  <|> ConstraintDeclaration_ClassConstraint <$> constraintDeclaration
  <?> "class_constraint"

classItemQualifier :: Parser ClassItemQualifier
classItemQualifier
  =   Static    <$ static
  <|> Protected <$ protected
  <|> Local     <$ local
  <?> "class_item_qualifier"

propertyQualifier :: Parser PropertyQualifier
propertyQualifier
  =   RandomQualifier_PropertyQualifier <$> randomQualifier
  <|> ClassItemQualifier_PropertyQualifier <$> classItemQualifier
  <?> "property_qualifier"

randomQualifier :: Parser RandomQualifier
randomQualifier
  =   Rand  <$ rand
  <|> Randc <$ randc
  <?> "random_qualifier"

methodQualifier :: Parser MethodQualifier
methodQualifier
  =   MethodQualifier
      <$> optional pure_
      <*  virtual_
  <|> ClassItemQualifier_MethodQualifier
      <$> classItemQualifier
  <?> "method_qualifier"

methodPrototype :: Parser MethodPrototype
methodPrototype
  =   TaskPrototype_MethodPrototype <$> taskPrototype
  <|> FunctionPrototype_MethodPrototype <$> functionPrototype
  <?> "method_prototype"

classConstructorDeclaration :: Parser ClassConstructorDeclaration
classConstructorDeclaration = ClassConstructorDeclaration
  <$> (function *> optional classScope)
  <*> (new *> optional (between lparen rparen (optional tfPortList)) <* semi)
  <*> many blockItemDeclaration
  <*> optional (super *> dot *> new *> optional (between lparen rparen listOfArguments) <* semi)
  <*> many functionStatementOrNull
  <*> (endfunction *> optional (colon *> new))
  <?> "class_constructor_declaration"

-- | A.1.10 Constraints
--
constraintDeclaration :: Parser ConstraintDeclaration
constraintDeclaration = ConstraintDeclaration
  <$> (optional static <* constraint)
  <*> constraintIdentifier
  <*> constraintBlock
  <?> "constraint_declaration"

constraintBlock :: Parser ConstraintBlock
constraintBlock = between lbrace rbrace (many constraintBlockItem)
  <?> "constraint_block"

constraintBlockItem :: Parser ConstraintBlockItem
constraintBlockItem
  =   SolveBeforeList_ConstraintBlockItem
      <$> (solve *> solveBeforeList)
      <*> (solve *> solveBeforeList)
      <*  semi
  <|> ConstraintExpression_ConstraintBlockItem
      <$> constraintExpression
  <?> "constraint_block_item"

solveBeforeList :: Parser SolveBeforeList
solveBeforeList = constraintPrimary `sepBy1` comma
  <?> "solve_before_list"

constraintPrimary :: Parser ConstraintPrimary
constraintPrimary
  =   ConstraintPrimary
      <$> optional (Left <$> implicitClassHandle <* dot <|> Right <$> classScope)
      <*> hierarchicalIdentifier
      <*> select
  <?> "constraint_primary"

constraintExpression :: Parser ConstraintExpression
constraintExpression
  =   ExpressionOrDist_ConstraintExpression
      <$> optional soft
      <*> expressionOrDist
      <*  semi
  <|> UniquenessConstraint_ConstraintExpression
      <$> uniquenessConstraint
      <*  semi
  <|> Expression_ConstraintExpression
      <$> expression
      <*> (arrow *> constraintSet)
  <|> IfElse_ConstraintExpression
      <$> (if_ *> between lparen rparen expression)
      <*> constraintSet
      <*> optional (else_ *> constraintSet)
  <|> Foreach_ConstraintExpression
      <$> (foreach *> lparen *> psOrHierarchicalArrayIdentifier)
      <*> (optional loopVariables <* rparen)
      <*> constraintSet
  <|> ConstraintPrimary_ConstraintExpression
      <$> (disable *> soft *> constraintPrimary)
      <*  semi
  <?> "constraint_expression"

uniquenessConstraint :: Parser UniquenessConstraint
uniquenessConstraint = unique *> many openRangeList
  <?> "uniqueness_constraint"

constraintSet :: Parser ConstraintSet
constraintSet
  =   pure <$> constraintExpression
  <|> between lbrace rbrace (many constraintExpression)
  <?> "constraint_set"

distList :: Parser DistList
distList = distItem `sepBy1` comma
  <?> "dist_list"

distItem :: Parser DistItem
distItem = DistItem
  <$> valueRange
  <*> optional distWeight
  <?> "dist_item"

distWeight :: Parser DistWeight
distWeight = DistWeight
  <$> (Left <$> dweq <|> Right <$> dwne)
  <*> expression
  <?> "dist_weight"

constraintPrototype :: Parser ConstraintPrototype
constraintPrototype = ConstraintPrototype
  <$> optional constraintPrototypeQualifier
  <*> optional static
  <*> (constraint *> constraintIdentifier)
  <*  semi
  <?> "contraint_prototype"

constraintPrototypeQualifier :: Parser ConstraintPrototypeQualifier
constraintPrototypeQualifier
  =   Extern <$ extern
  <|> Pure   <$ pure_
  <?> "constraint_prototype_qualifier"

externConstraintDeclaration :: Parser ExternConstraintDeclaration
externConstraintDeclaration = ExternConstraintDeclaration
  <$> optional static
  <*> (constraint *> classScope)
  <*> constraintIdentifier
  <*> constraintBlock
  <?> "extern_constraint_declaration"

identifierList :: Parser IdentifierList
identifierList = identifier `sepBy1` comma
  <?> "identifier_list"

-- | A.1.11 Package items
--
packageItem :: Parser PackageItem
packageItem
  =   PackageOrGenerateItemDeclaration_PackageItem <$> packageOrGenerateItemDeclaration
  <|> AnonymousProgram_PackageItem <$> anonymousProgram
  <|> PackageExportDeclaration_PackageItem <$> packageExportDeclaration
  <|> TimeunitsDeclaration_PackageItem <$> timeunitsDeclaration
  <?> "package_item"

packageOrGenerateItemDeclaration :: Parser PackageOrGenerateItemDeclaration
packageOrGenerateItemDeclaration
  =   NetDeclaration_PackageOrGenerateItemDeclaration <$> netDeclaration
  <|> DataDeclaration_PackageOrGenerateItemDeclaration <$> dataDeclaration
  <|> TaskDeclaration_PackageOrGenerateItemDeclaration <$> taskDeclaration
  <|> FunctionDeclaration_PackageOrGenerateItemDeclaration <$> functionDeclaration
  <|> CheckerDeclaration_PackageOrGenerateItemDeclaration <$> checkerDeclaration
  <|> DpiImportExport_PackageOrGenerateItemDeclaration <$> dpiImportExport
  <|> ExternConstraintDeclaration_PackageOrGenerateItemDeclaration
      <$> externConstraintDeclaration
  <|> ClassDeclaration_PackageOrGenerateItemDeclaration <$> classDeclaration
  <|> ClassConstructorDeclaration_PackageOrGenerateItemDeclaration
      <$> classConstructorDeclaration
  <|> LocalParameterDeclaration_PackageOrGenerateItemDeclaration
      <$> localParameterDeclaration
      <*  semi
  <|> ParameterDeclaration_PackageOrGenerateItemDeclaration
      <$> parameterDeclaration
      <*  semi
  <|> CovergroupDeclaration_PackageOrGenerateItemDeclaration <$> covergroupDeclaration
  <|> OverloadDeclaration_PackageOrGenerateItemDeclaration <$> overloadDeclaration
  <|> AssertionItemDeclaration_PackageOrGenerateItemDeclaration <$> assertionItemDeclaration
  <|> NoPackageOrGenerateItemDeclaration <$ semi
  <?> "package_or_generate_item_declaration"

anonymousProgram :: Parser AnonymousProgram
anonymousProgram = program *> semi *> many anonymousProgramItem <* endprogram
  <?> "anonymous_program"

anonymousProgramItem :: Parser AnonymousProgramItem
anonymousProgramItem
  =   TaskDeclaration_AnonymousProgramItem <$> taskDeclaration
  <|> FunctionDeclaration_AnonymousProgramItem <$> functionDeclaration
  <|> ClassDeclaration_AnonymousProgramItem <$> classDeclaration
  <|> CovergroupDeclaration_AnonymousProgramItem <$> covergroupDeclaration
  <|> ClassConstructorDeclaration_AnonymousProgramItem <$> classConstructorDeclaration
  <|> NoAnonymousProgramItem <$ semi
  <?> "anonymous_program_item"


-- | A.2 Declarations
--
--   A.2.1 Declaration types
--
--   A.2.1.1 Module parameter declarations
--

localParameterDeclaration :: Parser LocalParameterDeclaration
localParameterDeclaration
  =   DataTypeOrImplicit_LocalParameterDeclaration
      <$> (localparam *> dataTypeOrImplicit)
      <*> listOfParamAssignments
  <|> ListOfTypeAssignments_LocalParameterDeclaration
      <$> (localparam *> type_ *> listOfTypeAssignments)
  <?> "local_parameter_declaration" 

parameterDeclaration :: Parser ParameterDeclaration
parameterDeclaration
  =   DataTypeOrImplicit_ParameterDeclaration
      <$> (parameter *> dataTypeOrImplicit)
      <*> listOfParamAssignments
  <|> ListOfTypeAssignments_ParameterDeclaration
      <$> (parameter *> type_ *> listOfTypeAssignments)
  <?> "parameter_declaration" 

specparamDeclaration :: Parser SpecparamDeclaration
specparamDeclaration = SpecparamDeclaration
  <$> (specparam *> optional packedDimension)
  <*> listOfSpecparamAssignments
  <*  semi
  <?> "specparam_declaration"

-- | A.2.1.2 Port declarations
--
inoutDeclaration :: Parser InoutDeclaration
inoutDeclaration = InoutDeclaration
  <$> (inout *> netPortType)
  <*> listOfPortIdentifiers
  <?> "inout_declaration"

inputDeclaration :: Parser InputDeclaration
inputDeclaration = InputDeclaration
  <$> (input *> (Left <$> netPortType <|> Right <$> variablePortType))
  <*> listOfPortIdentifiers
  <?> "input_declaration"

outputDeclaration :: Parser OutputDeclaration
outputDeclaration = OutputDeclaration
  <$> (output *> (Left <$> netPortType <|> Right <$> variablePortType))
  <*> listOfPortIdentifiers
  <?> "output_declaration"

interfacePortDeclaration :: Parser InterfacePortDeclaration
interfacePortDeclaration =  InterfacePortDeclaration
  <$> interfaceIdentifier
  <*> optional (dot *> modportIdentifier)
  <*> listOfInterfaceIdentifiers
  <?> "interface_port_declaration"

refDeclaration :: Parser RefDeclaration
refDeclaration = RefDeclaration
  <$> (ref *> variablePortType)
  <*> listOfVariableIdentifiers
  <?> "ref_declaration"

-- | A.2.1.3  Type declarations
--
dataDeclaration :: Parser DataDeclaration
dataDeclaration
  =   DataDeclaration
      <$> optional const_
      <*> optional var
      <*> optional lifetime
      <*> dataTypeOrImplicit
      <*> listOfVariableDeclAssignments
  <|> TypeDeclaration_DataDeclaration
      <$> typeDeclaration
  <|> NetTypeDeclaration_DataDeclaration
      <$> packageImportDeclaration
      <*> netTypeDeclaration
  <?> "data_declaration"

packageImportDeclaration :: Parser PackageImportDeclaration
packageImportDeclaration = import_ *> sepBy1 packageImportItem comma <* semi
  <?> "package_import_declaration"

packageImportItem :: Parser PackageImportItem
packageImportItem = PackageImportItem
  <$> packageIdentifier
  <*> (namequal >> Just <$> identifier <|> Nothing <$ star)
  <?> "package_import_item"

packageExportDeclaration :: Parser PackageExportDeclaration
packageExportDeclaration
  =   (export *> (packageImportItem `sepBy1` comma <|> [] <$ star <* namequal <* star))
  <*  semi
  <?> "package_export_declaration"

genvarDeclaration :: Parser GenvarDeclaration
genvarDeclaration = genvar *> listOfGenvarIdentifiers <* semi
  <?> "genvar_declaration"

netDeclaration :: Parser NetDeclaration
netDeclaration
  =   NetType_NetDeclaration
      <$> netType
      <*> optional (Left <$> driveStrength <|> Right <$> chargeStrength)
      <*> optional (Vectored <$ vectored <|> Scalared <$ scalared)
      <*> dataTypeOrImplicit
      <*> optional delay3
      <*> listOfNetDeclAssignments
      <*  semi
  <|> NetDeclaration
      <$> netTypeIdentifier
      <*> optional delayControl
      <*> listOfNetDeclAssignments
      <*  semi
  <|> ImplicitDataType_NetDeclaration
      <$> (interconnect *> implicitDataType)
      <*> optional delayValue
      <*> ((,) <$> netIdentifier <*> many unpackedDimension)
      <*> optional (comma >> (,) <$> netIdentifier <*> many unpackedDimension)
      <*  semi
  <?> "net_declaration"

typeDeclaration :: Parser TypeDeclaration
typeDeclaration
  =   DataType_TypeDeclaration
      <$> (typedef *> dataType)
      <*> typeIdentifier
      <*> many variableDimension
      <*  semi
  <|> InterfaceInstance_TypeDeclaration
      <$> (typedef *> interfaceInstanceIdentifier)
      <*> (constantBitSelect <* dot)
      <*> typeIdentifier
      <*> typeIdentifier
      <*  semi
  <|> TypeDeclaration
      <$> (typedef *> optional typeKeyword)
      <*> typeIdentifier
      <*  semi
  <?> "type_declaration"
  where
  typeKeyword
    =   Enum   <$ enum
    <|> Struct <$ struct
    <|> Union  <$ union
    <|> Class  <$ class_
    <|> InterfaceClass <$ interface <* class_

netTypeDeclaration :: Parser NetTypeDeclaration
netTypeDeclaration
  =   DataType_NetTypeDeclaration
      <$> (nettype *> dataType)
      <*> netTypeIdentifier
      <*> optional (with >> (,) <$> optional scope <*> tfIdentifier)
      <*  semi
  <|> NetTypeDeclaration
      <$> (nettype *> optional scope)
      <*> netTypeIdentifier
      <*> netTypeIdentifier
      <*  semi
  <?> "net_type_declaration"
  where scope = Left <$> packageScope <|> Right <$> classScope

lifetime :: Parser Lifetime
lifetime
  =   StaticLifetime    <$ static
  <|> AutomaticLifetime <$ automatic
  <?> "lifetime"

-- | A.2.2 Declaration types
--
--   A.2.2.1 Net and variable types
--
castingType :: Parser CastingType
castingType
  =   SimpleType_CastingType <$> simpleType
  <|> ConstantPrimary_CastingType <$> constantPrimary
  <|> Signing_CastingType <$> signing
  <|> StringCastingType <$ string
  <|> ConstCastingType <$ const_
  <?> "casting_type"

dataType :: Parser DataType
dataType
  =   IntegerVectorType_DataType
      <$> integerVectorType
      <*> optional signing
      <*> many packedDimension
  <|> IntegerAtomType_DataType
      <$> integerAtomType
      <*> optional signing
  <|> NonIntegerType_DataType
      <$> nonIntegerType
  <|> StructUnion_DataType
      <$> structUnion
      <*> optional (packed *> optional signing)
      <*> between lbrace rbrace (many1 structUnionMember)
      <*> many packedDimension
  <|> Enum_DataType
      <$> optional enumBaseType
      <*> between lbrace rbrace (enumNameDeclaration `sepBy1` comma)
      <*> many packedDimension
  <|> StringDataType <$ string
  <|> ChandleDataType <$ chandle
  <|> Interface_DataType
      <$> (virtual_ *> optional interface)
      <*> interfaceIdentifier
      <*> optional parameterValueAssignment
      <*> optional modportIdentifier
  <|> Type_DataType
      <$> optional (Left <$> classScope <|> Right <$> packageScope)
      <*> typeIdentifier
      <*> many packedDimension
  <|> ClassType_DataType <$> classType
  <|> EventDataType <$ event
  <|> PsCovergroup_DataType <$> psCovergroupIdentifier
  <|> TypeReference_DataType <$> typeReference
  <?> "data_type"

dataTypeOrImplicit :: Parser DataTypeOrImplicit
dataTypeOrImplicit
  =   DataType_DataTypeOrImplicit <$> dataType
  <|> ImplicitDataType_DataTypeOrImplicit <$> implicitDataType
  <?> "data_type_or_implicit"

implicitDataType :: Parser ImplicitDataType
implicitDataType = ImplicitDataType
  <$> optional signing
  <*> many packedDimension
  <?> "implicit_data_type"

enumBaseType :: Parser EnumBaseType
enumBaseType
  =   IntegerAtomType_EnumBaseType
      <$> integerAtomType
      <*> optional signing
  <|> IntegerVectorType_EnumBaseType
      <$> integerVectorType
      <*> optional signing
      <*> optional packedDimension
  <|> Type_EnumBaseType
      <$> typeIdentifier
      <*> optional packedDimension
  <?> "enum_base_type"

enumNameDeclaration :: Parser EnumNameDeclaration
enumNameDeclaration = EnumNameDeclaration
  <$> enumIdentifier
  <*> optional (between lbrack rbrack num)
  <*> optional (assign_op *> constantExpression)
  <?> "enum_name_declaration"
  where num = (,) <$> integralNumber <*> optional (colon *> integralNumber)

classScope :: Parser ClassScope
classScope = classType <* namequal
  <?> "class_scope"

classType :: Parser ClassType
classType = ClassType
  <$> psClassIdentifier
  <*> optional parameterValueAssignment
  <*> many (namequal >> (,) <$> classIdentifier <*> optional parameterValueAssignment)
  <?> "class_type"

integerType :: Parser IntegerType
integerType
  =   IntegerVectorType_IntegerType <$> integerVectorType
  <|> IntegerAtomType_IntegerType <$> integerAtomType
  <?> "integer_type"

integerAtomType :: Parser IntegerAtomType
integerAtomType
  =   TByte     <$ byte
  <|> TShortint <$ shortint
  <|> TInt      <$ int
  <|> TLongint  <$ longint
  <|> TInteger  <$ integer
  <|> TTime     <$ time
  <?> "integer_atom_type"

integerVectorType :: Parser IntegerVectorType
integerVectorType
  =   TBit   <$ bit
  <|> TLogic <$ logic
  <|> TReg   <$ reg
  <?> "integer_vector_type"

nonIntegerType :: Parser NonIntegerType
nonIntegerType
  =   TShortreal <$ shortreal
  <|> TReal      <$ real
  <|> TRealtime  <$ realtime
  <?> "non_integer_type"

netType :: Parser NetType
netType
  =   TSupply0 <$ supply0
  <|> TSupply1 <$ supply1
  <|> Tri      <$ tri
  <|> Triand   <$ triand
  <|> Trior    <$ trior
  <|> Trireg   <$ trireg
  <|> Tri0     <$ tri0
  <|> Tri1     <$ tri1
  <|> Uwire    <$ uwire
  <|> Wire     <$ wire
  <|> Wand     <$ wand
  <|> Wor      <$ wor
  <?> "net_type"

netPortType :: Parser NetPortType
netPortType
  =   DataTypeOrImplicit_NetPortType
      <$> optional netType
      <*> dataTypeOrImplicit
  <|> NetType_NetPortType
      <$> netTypeIdentifier
  <|> ImplicitDataType_NetPortType
      <$> (interconnect *> implicitDataType)
  <?> "net_port_type"

variablePortType :: Parser VariablePortType
variablePortType = varDataType
  <?> "variable_port_type"

varDataType :: Parser VarDataType
varDataType
  =   DataType_VarDataType <$> dataType
  <|> DataTypeOrImplicit_VarDataType <$> (var *> dataTypeOrImplicit)
  <?> "var_data_type"

signing :: Parser Signing
signing = Signed <$ signed <|> Unsigned <$ unsigned
  <?> "signing"

simpleType :: Parser SimpleType
simpleType
  =   IntegerType_SimpleType <$> integerType
  <|> NonIntegerType_SimpleType <$> nonIntegerType
  <|> PsType_SimpleType <$> psTypeIdentifier
  <|> PsParameter_SimpleType <$> psParameterIdentifier
  <?> "simple_type"

structUnionMember :: Parser StructUnionMember
structUnionMember = StructUnionMember
  <$> many attributeInstance
  <*> optional randomQualifier
  <*> dataTypeOrVoid
  <*> listOfVariableDeclAssignments
  <*  semi
  <?> "struct_union_member"

dataTypeOrVoid :: Parser DataTypeOrVoid
dataTypeOrVoid = DataType_DataTypeOrVoid <$> dataType <|> VoidDataType <$ void_
  <?> "data_type_or_void"

structUnion :: Parser StructUnion
structUnion = TStruct <$ struct <|> TUnion <$> (union *> optional tagged)
  <?> "struct_union"

typeReference :: Parser TypeReference
typeReference
  =   Expression_TypeReference <$> (type_ *> between lparen rparen expression)
  <|> DataType_TypeReference <$> (type_ *> between lparen rparen dataType)
  <?> "type_reference"

-- | A.2.2.2 Strengths
--
driveStrength :: Parser DriveStrength
driveStrength
  =   between lparen rparen (Strength0_Strength1_DriveStrength <$> strength0 <* comma <*> strength1)
  <|> between lparen rparen (Strength1_Strength0_DriveStrength <$> strength1 <* comma <*> strength0)
  <?> "drive_strength"

strength0 :: Parser Strength0
strength0
  =   Supply0 <$ supply0
  <|> Strong0 <$ strong0
  <|> Pull0   <$ pull0
  <|> Weak0   <$ weak0
  <|> Highz0  <$ highz0
  <?> "strength0"

strength1 :: Parser Strength1
strength1
  =   Supply1 <$ supply1
  <|> Strong1 <$ strong1
  <|> Pull1   <$ pull1
  <|> Weak1   <$ weak1
  <|> Highz1  <$ highz1
  <?> "strength1"

chargeStrength :: Parser ChargeStrength
chargeStrength
  =   Small  <$ small
  <|> Medium <$ medium
  <|> Large  <$ large
  <?> "charge_strength"

-- | A.2.2.3 Delays
--

delay3 :: Parser Delay3
delay3
  =   DelayValue_Delay3
      <$> (hash *> delayValue)
  <|> Delay3
      <$> between lparen rparen
          ((,) <$> (comma *> mintypmaxExpression) <*> optional
            ((,) <$> (comma *> mintypmaxExpression) <*> optional mintypmaxExpression))
  <?> "delay3"

delay2 :: Parser Delay2
delay2
  =   DelayValue_Delay2
      <$> (hash *> delayValue)
  <|> Delay2
      <$> between lparen rparen
          ((,) <$> (comma *> mintypmaxExpression) <*> optional (comma *> mintypmaxExpression))
  <?> "delay2"

delayValue :: Parser DelayValue
delayValue
  =   UnsignedNumber_DelayValue <$> unsignedNumber
  <|> RealNumber_DelayValue <$> realNumber
  <|> PsIdentifier_DelayValue <$> psIdentifier
  <|> TimeLiteral_DelayValue <$> timeLiteral
  <|> Step1 <$ step1
  <?> "delay_value"


-- | A.2.3 Declaration lists
--

listOfDefparamAssignments :: Parser ListOfDefparamAssignments
listOfDefparamAssignments = defparamAssignment `sepBy1` comma
  <?> "list_of_defparam_assignments"

listOfGenvarIdentifiers :: Parser ListOfGenvarIdentifiers
listOfGenvarIdentifiers = genvarIdentifier `sepBy1` comma
  <?> "list_of_genvar_identifiers"

listOfInterfaceIdentifiers :: Parser ListOfInterfaceIdentifiers
listOfInterfaceIdentifiers = item `sepBy1` comma
  <?> "list_of_interface_identifiers"
  where item = (,) <$> interfaceIdentifier <*> many unpackedDimension

listOfNetDeclAssignments :: Parser ListOfNetDeclAssignments
listOfNetDeclAssignments = netDeclAssignment `sepBy1` comma
  <?> "list_of_net_decl_assignments"

listOfParamAssignments :: Parser ListOfParamAssignments
listOfParamAssignments = paramAssignment `sepBy1` comma
  <?> "list_of_param_assignments"

listOfPortIdentifiers :: Parser ListOfPortIdentifiers
listOfPortIdentifiers = item `sepBy1` comma
  <?> "list_of_port_identifiers"
  where item = (,) <$> portIdentifier <*> many unpackedDimension

listOfUdpPortIdentifiers :: Parser ListOfUdpPortIdentifiers
listOfUdpPortIdentifiers = portIdentifier `sepBy1` comma
  <?> "list_of_udp_port_identifiers"

listOfSpecparamAssignments :: Parser ListOfSpecparamAssignments
listOfSpecparamAssignments = specparamAssignment `sepBy1` comma
  <?> "list_of_specparam_assignments"

listOfTfVariableIdentifiers :: Parser ListOfTfVariableIdentifiers
listOfTfVariableIdentifiers = item `sepBy1` comma
  <?> "list_of_tf_variable_identifiers"
  where
  item = (,,)
    <$> portIdentifier
    <*> many variableDimension
    <*> optional (assign_op *> expression)

listOfTypeAssignments :: Parser ListOfTypeAssignments
listOfTypeAssignments = typeAssignment `sepBy1` comma
  <?> "list_of_type_assignments"

listOfVariableDeclAssignments :: Parser ListOfVariableDeclAssignments
listOfVariableDeclAssignments = variableDeclAssignment `sepBy1` comma
  <?> "list_of_variable_decl_assignments"

listOfVariableIdentifiers :: Parser ListOfVariableIdentifiers
listOfVariableIdentifiers = item `sepBy1` comma
  <?> "list_of_variable_identifiers"
  where item = (,) <$> variableIdentifier <*> many variableDimension

listOfVariablePortIdentifiers :: Parser ListOfVariablePortIdentifiers
listOfVariablePortIdentifiers = item `sepBy1` comma
  <?> "list_of_variable_port_identifiers"
  where
  item = (,,)
    <$> portIdentifier
    <*> many variableDimension
    <*> optional (assign_op *> constantExpression)


-- | A.2.4 Declaration assignments
--

defparamAssignment :: Parser DefparamAssignment
defparamAssignment = DefparamAssignment
  <$> hierarchicalParameterIdentifier
  <*> (assign_op *> constantMintypmaxExpression)
  <?> "defparam_assignment"

netDeclAssignment :: Parser NetDeclAssignment
netDeclAssignment = NetDeclAssignment
  <$> netIdentifier
  <*> many unpackedDimension
  <*> optional (assign_op *> expression)
  <?> "net_decl_assignment"

paramAssignment :: Parser ParamAssignment
paramAssignment = ParamAssignment
  <$> parameterIdentifier
  <*> many unpackedDimension
  <*> optional (assign_op *> constantParamExpression)
  <?> "param_assignment"

specparamAssignment :: Parser SpecparamAssignment
specparamAssignment
  =   SpecparamAssignment
      <$> specparamIdentifier
      <*> (assign_op *> constantMintypmaxExpression)
  <|> PulseControlSpecparam_SpecparamAssignment
      <$> pulseControlSpecparam
  <?> "specparam_assignment"

typeAssignment :: Parser TypeAssignment
typeAssignment = TypeAssignment
  <$> typeIdentifier
  <*> optional (assign_op *> dataType)
  <?> "type_assignment"

-- !
pulseControlSpecparam :: Parser PulseControlSpecparam
pulseControlSpecparam = PulseControlSpecparam
  <$> pure Nothing
  <*> (pathpulse *> assign_op *> lparen *> rejectLimitValue)
  <*> optional (comma *> errorLimitValue)
  <?> "pulse_control_specparam"

errorLimitValue :: Parser ErrorLimitValue
errorLimitValue = limitValue
  <?> "error_limit_value"

rejectLimitValue :: Parser RejectLimitValue
rejectLimitValue = limitValue
  <?> "reject_limit_value"

limitValue :: Parser LimitValue
limitValue = constantMintypmaxExpression
  <?> "limit_value"

variableDeclAssignment :: Parser VariableDeclAssignment
variableDeclAssignment
  =   VariableDeclAssignment
      <$> variableIdentifier
      <*> many variableDimension
      <*> optional (assign_op *> expression)
  <|> DynamicArrayVariableIdentifier_VariableDeclAssignment
      <$> dynamicArrayVariableIdentifier
      <*> unsizedDimension
      <*> many variableDimension
      <*> optional (assign_op *> dynamicArrayNew)
  <|> ClassVariableIdentifier_VariableDeclAssignment
      <$> classVariableIdentifier
      <*> optional (assign_op *> classNew)
  <?> "variable_decl_assignment"

classNew :: Parser ClassNew
classNew
  =   ClassNew
      <$> (optional classScope <* new)
      <*> optional (between lparen rparen listOfArguments)
  <|> Expression_ClassNew
      <$> (new *> expression)
  <?> "class_new"

dynamicArrayNew :: Parser DynamicArrayNew
dynamicArrayNew = DynamicArrayNew
  <$> (new *> between lbrack rbrack expression)
  <*> optional (between lparen rparen expression)
  <?> "dynamic_array_new"


-- | A.2.5 Declaration ranges
--

unpackedDimension :: Parser UnpackedDimension
unpackedDimension
  =   ConstantRange_UnpackedDimension
      <$> between lbrack rbrack constantRange
  <|> ConstantExpression_UnpackedDimension
      <$> between lbrack rbrack constantExpression
  <?> "unpacked_dimension"

packedDimension :: Parser PackedDimension
packedDimension
  =   ConstantRange_PackedDimension
      <$> between lbrack rbrack constantRange
  <|> UnsizedDimension_PackedDimension
      <$> unsizedDimension
  <?> "packed_dimension"

associativeDimension :: Parser AssociativeDimension
associativeDimension = between lbrack rbrack (Just <$> dataType <|> Nothing <$ star)
  <?> "associative_dimension"

variableDimension :: Parser VariableDimension
variableDimension
  =   UnsizedDimension_VariableDimension <$> unsizedDimension
  <|> UnpackedDimension_VariableDimension <$> unpackedDimension
  <|> AssociativeDimension_VariableDimension <$> associativeDimension
  <|> QueueDimension_VariableDimension <$> queueDimension
  <?> "variable_dimension"

queueDimension :: Parser QueueDimension
queueDimension = between lbrack rbrack (dollar *> optional (colon *> constantExpression))
  <?> "queue_dimension"

unsizedDimension :: Parser UnsizedDimension
unsizedDimension = lbrack *> rbrack
  <?> "unsized_dimension"


-- | A.2.6 Function declarations
--
functionDataTypeOrImplicit :: Parser FunctionDataTypeOrImplicit
functionDataTypeOrImplicit
  =   DataTypeOrVoid_FunctionDataTypeOrImplicit <$> dataTypeOrVoid
  <|> ImplicitDataType_FunctionDataTypeOrImplicit <$> implicitDataType
  <?> "function_data_type_or_implicit"

functionDeclaration :: Parser FunctionDeclaration
functionDeclaration = FunctionDeclaration
  <$> optional lifetime
  <*> functionBodyDeclaration
  <?> "function_declaration"

functionBodyDeclaration :: Parser FunctionBodyDeclaration
functionBodyDeclaration
  =   FunctionBodyDeclaration
      <$> functionDataTypeOrImplicit
      <*> optional (Left <$> interfaceIdentifier <* dot <|> Right <$> classScope)
      <*> (functionIdentifier <* semi)
      <*> pure Nothing
      <*> many tfItemDeclaration
      <*> pure [] 
      <*> many functionStatementOrNull
      <*> (endfunction *> optional (colon *> functionIdentifier))
  <|> FunctionBodyDeclaration
      <$> functionDataTypeOrImplicit
      <*> optional (Left <$> interfaceIdentifier <* dot <|> Right <$> classScope)
      <*> functionIdentifier
      <*> (between lparen rparen (optional tfPortList) <* semi)
      <*> pure []
      <*> many blockItemDeclaration
      <*> many functionStatementOrNull
      <*> (endfunction *> optional (colon *> functionIdentifier))
  <?> "function_body_declaration"

functionPrototype :: Parser FunctionPrototype
functionPrototype = FunctionPrototype
  <$> (function *> dataTypeOrVoid)
  <*> functionIdentifier
  <*> optional (between lparen rparen (optional tfPortList))
  <?> "function_prototype"

dpiImportExport :: Parser DpiImportExport
dpiImportExport
  =   DpiFunctionProto_DpiImportExport
      <$> (import_ *> dpiSpecString)
      <*> optional dpiFunctionImportProperty
      <*> optional (cIdentifier <* assign_op)
      <*> dpiFunctionProto
      <*  semi
  <|> DpiTaskProto_DpiImportExport
      <$> (import_ *> dpiSpecString)
      <*> optional dpiTaskImportProperty
      <*> optional (cIdentifier <* assign_op)
      <*> dpiTaskProto
      <*  semi
  <|> FunctionIdentifier_DpiImportExport
      <$> (export *> dpiSpecString)
      <*> optional (cIdentifier <* assign_op)
      <*> (function *> functionIdentifier)
      <*  semi
  <|> TaskIdentifier_DpiImportExport
      <$> (export *> dpiSpecString)
      <*> optional (cIdentifier <* assign_op)
      <*> (task *> taskIdentifier)
      <*  semi
  <?> "dpi_import_export"

dpiSpecString :: Parser DpiSpecString
dpiSpecString = stringLiteral
  <?> "dpi_spec_string"

dpiFunctionImportProperty :: Parser DpiFunctionImportProperty
dpiFunctionImportProperty = Context <$ context <|> Pure <$ pure_
  <?> "dpi_function_import_property"

dpiTaskImportProperty :: Parser DpiTaskImportProperty
dpiTaskImportProperty = Context <$ context
  <?> "dpi_task_import_property"

dpiFunctionProto :: Parser DpiFunctionProto
dpiFunctionProto = functionPrototype
  <?> "dpi_function_proto"

dpiTaskProto :: Parser DpiTaskProto
dpiTaskProto = taskPrototype
  <?> "dpi_task_proto"


-- | A.2.7 Task declarations
--
taskDeclaration :: Parser TaskDeclaration
taskDeclaration = TaskDeclaration
  <$> (task *> optional lifetime)
  <*> taskBodyDeclaration
  <?> "task_declaration"

taskBodyDeclaration :: Parser TaskBodyDeclaration
taskBodyDeclaration
  =   TaskBodyDeclaration
      <$> optional (Left <$> interfaceIdentifier <* dot <|> Right <$> classScope)
      <*> (taskIdentifier <* semi)
      <*> pure Nothing
      <*> many tfItemDeclaration
      <*> pure [] 
      <*> many statementOrNull
      <*> (endtask *> optional (colon *> taskIdentifier))
  <|> TaskBodyDeclaration
      <$> optional (Left <$> interfaceIdentifier <* dot <|> Right <$> classScope)
      <*> taskIdentifier
      <*> (between lparen rparen (optional tfPortList) <* semi)
      <*> pure []
      <*> many blockItemDeclaration
      <*> many statementOrNull
      <*> (endtask *> optional (colon *> taskIdentifier))
  <?> "task_body_declaration"

tfItemDeclaration :: Parser TfItemDeclaration
tfItemDeclaration
  =   BlockItemDeclaration_TfItemDeclaration <$> blockItemDeclaration
  <|> TfPortDeclaration_TfItemDeclaration <$> tfPortDeclaration
  <?> "tf_item_declaration"

tfPortList :: Parser TfPortList
tfPortList = tfPortItem `sepBy1` comma
  <?> "tf_port_list"

tfPortItem :: Parser TfPortItem
tfPortItem = TfPortItem
  <$> many attributeInstance
  <*> optional tfPortDirection
  <*> optional var
  <*> dataTypeOrImplicit
  <*> optional
      ((,,) <$> portIdentifier <*> many variableDimension <*> optional (assign_op *> expression))
  <?> "tf_port_item"

tfPortDirection :: Parser TfPortDirection
tfPortDirection
  =   PortDirection_TfPortDirection <$> portDirection
  <|> ConstRef <$ const_ <* ref
  <?> "tf_port_direction"

tfPortDeclaration :: Parser TfPortDeclaration
tfPortDeclaration = TfPortDeclaration
  <$> many attributeInstance
  <*> tfPortDirection
  <*> optional var
  <*> dataTypeOrImplicit
  <*> listOfTfVariableIdentifiers
  <*  semi
  <?> "tf_port_declaration"

taskPrototype :: Parser TaskPrototype
taskPrototype = TaskPrototype
  <$> (task *> taskIdentifier)
  <*> optional (between lparen rparen (optional tfPortList))
  <?> "task_prototype"


-- | A.2.8 Block item declarations
--
blockItemDeclaration :: Parser BlockItemDeclaration
blockItemDeclaration
  =   DataDeclaration_BlockItemDeclaration
      <$> many attributeInstance
      <*> dataDeclaration
  <|> LocalParameterDeclaration_BlockItemDeclaration 
      <$> many attributeInstance
      <*> localParameterDeclaration
      <*  semi
  <|> ParameterDeclaration_BlockItemDeclaration 
      <$> many attributeInstance
      <*> parameterDeclaration
      <*  semi
  <|> OverloadDeclaration_BlockItemDeclaration 
      <$> many attributeInstance
      <*> overloadDeclaration
  <|> LetDeclaration_BlockItemDeclaration 
      <$> many attributeInstance
      <*> letDeclaration
  <?> "block_item_declaration"

overloadDeclaration :: Parser OverloadDeclaration
overloadDeclaration = OverloadDeclaration
  <$> (bind *> overloadOperator)
  <*> (function *> dataType)
  <*> functionIdentifier
  <*> between lparen rparen overloadProtoFormals
  <*  semi
  <?> "overload_declaration"

overloadOperator :: Parser OverloadOperator
overloadOperator
  =   PlusOverload  <$ plus  <|> IncrementOverload  <$ increment
  <|> MinusOverload <$ minus <|> DecrementOverload  <$ decrement
  <|> StarOverload  <$ star  <|> DoublestarOverload <$ doublestar
  <|> SlashOverload <$ slash
  <|> PercentOverload <$ percent
  <|> EqOverload <$ eq <|> NotEqOverload <$ noteq
  <|> LtOverload <$ lt <|> LtEqOverload  <$ lteq
  <|> GtOverload <$ gt <|> GtEqOverload  <$ gteq
  <|> AssignOverload <$ assign_op
  <?> "overload_operator"

overloadProtoFormals :: Parser OverloadProtoFormals
overloadProtoFormals = dataType `sepBy1` comma
  <?> "overload_proto_formals"


-- | A.2.9 Interface declarations
--

modportDeclaration :: Parser ModportDeclaration
modportDeclaration = modport *> sepBy1 modportItem comma <* semi
  <?> "modport_declaration"

modportItem :: Parser ModportItem
modportItem = ModportItem
  <$> modportIdentifier
  <*> between lparen rparen (modportPortsDeclaration `sepBy1` comma)
  <?> "modport_item"

modportPortsDeclaration :: Parser ModportPortsDeclaration
modportPortsDeclaration
  =   ModportSimplePortsDeclaration_ModportPortsDeclaration
      <$> many attributeInstance
      <*> modportSimplePortsDeclaration
  <|> ModportTfPortsDeclaration_ModportPortsDeclaration
      <$> many attributeInstance
      <*> modportTfPortsDeclaration
  <|> ModportClockingDeclaration_ModportPortsDeclaration
      <$> many attributeInstance
      <*> modportClockingDeclaration
  <?> "modport_ports_declaration"

modportClockingDeclaration :: Parser ModportClockingDeclaration
modportClockingDeclaration = clocking_ *> clockingIdentifier
  <?> "modport_clocking_declaration"

modportSimplePortsDeclaration :: Parser ModportSimplePortsDeclaration
modportSimplePortsDeclaration = (,) 
  <$> portDirection
  <*> sepBy1 modportSimplePort comma
  <?> "modport_simple_ports_declaration"

modportSimplePort :: Parser ModportSimplePort
modportSimplePort
  =   ModportSimplePort
      <$> portIdentifier
      <*> pure Nothing
  <|> ModportSimplePort
      <$> (dot *> portIdentifier)
      <*> between lparen rparen (optional expression)
  <?> "modport_simple_port"

modportTfPortsDeclaration :: Parser ModportTfPortsDeclaration
modportTfPortsDeclaration = (,)
  <$> importExport
  <*> sepBy1 modportTfPort comma
  <?> "modport_tf_ports_declaration"

modportTfPort :: Parser ModportTfPort
modportTfPort
  =   MethodPrototype_ModportTfPort <$> methodPrototype
  <|> TfIdentifier_ModportTfPort <$> tfIdentifier
  <?> "modport_tf_port"

importExport :: Parser ImportExport
importExport = Import <$ import_ <|> Export <$ export
  <?> "import_export"


-- | A.2.10 Assertion declarations
--

concurrentAssertionItem :: Parser ConcurrentAssertionItem
concurrentAssertionItem
  =   ConcurrentAssertionStatement_ConcurrentAssertionItem
      <$> optional (blockIdentifier <* colon)
      <*> concurrentAssertionStatement
  <|> CheckerInstantiation_ConcurrentAssertionItem
      <$> checkerInstantiation
  <?> "concurrent_assertion_item"

concurrentAssertionStatement :: Parser ConcurrentAssertionStatement
concurrentAssertionStatement
  =   AssertPropertyStatement_ConcurrentAssertionStatement <$> assertPropertyStatement
  <|> AssumePropertyStatement_ConcurrentAssertionStatement <$> assumePropertyStatement
  <|> CoverPropertyStatement_ConcurrentAssertionStatement <$> coverPropertyStatement
  <|> CoverSequenceStatement_ConcurrentAssertionStatement <$> coverSequenceStatement
  <|> RestrictPropertyStatement_ConcurrentAssertionStatement <$> restrictPropertyStatement
  <?> "concurrent_assertion_statement"

assertPropertyStatement :: Parser AssertPropertyStatement
assertPropertyStatement = AssertPropertyStatement
  <$> (assert *> property *> between lparen rparen propertySpec)
  <*> actionBlock
  <?> "assert_property_statement"

assumePropertyStatement :: Parser AssumePropertyStatement
assumePropertyStatement = AssumePropertyStatement
  <$> (assume *> property *> between lparen rparen propertySpec)
  <*> actionBlock
  <?> "assume_property_statement"

coverPropertyStatement :: Parser CoverPropertyStatement
coverPropertyStatement = CoverPropertyStatement
  <$> (cover *> property *> between lparen rparen propertySpec)
  <*> statementOrNull
  <?> "cover_property_statement"

expectPropertyStatement :: Parser ExpectPropertyStatement
expectPropertyStatement = ExpectPropertyStatement
  <$> (expect *> between lparen rparen propertySpec)
  <*> actionBlock
  <?> "expect_property_statement"

coverSequenceStatement :: Parser CoverSequenceStatement
coverSequenceStatement = CoverSequenceStatement
  <$> (cover *> sequence__ *> lparen *> optional clockingEvent)
  <*> optional (disable *> iff *> between lparen rparen expressionOrDist)
  <*> (sequenceExpr <* rparen)
  <*> statementOrNull
  <?> "cover_sequence_statement"

restrictPropertyStatement :: Parser RestrictPropertyStatement
restrictPropertyStatement = restrict *> between lparen rparen propertySpec <* semi
  <?> "restrict_property_statement"

propertyInstance :: Parser PropertyInstance
propertyInstance = PropertyInstance
  <$> psOrHierarchicalPropertyIdentifier
  <*> optional (between lparen rparen (optional propertyListOfArguments))
  <?> "property_instance"

propertyListOfArguments :: Parser PropertyListOfArguments
propertyListOfArguments
  =   PropertyListOfArguments
      <$> sepBy (optional propertyActualArg) comma
      <*> optional (comma *> sepBy1 item comma)
  <|> PropertyListOfArguments
      <$> pure []
      <*> (Just <$> sepBy1 item comma)
  <?> "property_list_of_arguments"
  where item = (,) <$> (dot *> identifier) <*> between lparen rparen (optional propertyActualArg)

propertyActualArg :: Parser PropertyActualArg
propertyActualArg
  =   PropertyExpr_PropertyActualArg <$> propertyExpr
  <|> SequenceActualArg_PropertyActualArg <$> sequenceActualArg
  <?> "property_actual_arg"

assertionItemDeclaration :: Parser AssertionItemDeclaration
assertionItemDeclaration
  =   PropertyDeclaration_AssertionItemDeclaration <$> propertyDeclaration
  <|> SequenceDeclaration_AssertionItemDeclaration <$> sequenceDeclaration
  <|> LetDeclaration_AssertionItemDeclaration <$> letDeclaration
  <?> "assertion_item_declaration"

propertyDeclaration :: Parser PropertyDeclaration
propertyDeclaration = PropertyDeclaration
  <$> (property *> propertyIdentifier)
  <*> optional (between lparen rparen (optional propertyPortList))
  <*> (semi *> many assertionVariableDeclaration)
  <*> (propertySpec <* optional semi)
  <*> (endproperty *> optional propertyIdentifier)
  <?> "property_declaration"

propertyPortList :: Parser PropertyPortList
propertyPortList = propertyPortItem `sepBy1` comma
  <?> "property_port_list"

propertyPortItem :: Parser PropertyPortItem
propertyPortItem = PropertyPortItem
  <$> many attributeInstance
  <*> optional (local *> optional (propertyLvarPortDirection))
  <*> propertyFormalType
  <*> formalPortIdentifier
  <*> many variableDimension
  <*> optional (assign_op *> propertyActualArg)
  <?> "property_port_item"

propertyLvarPortDirection :: Parser PropertyLvarPortDirection
propertyLvarPortDirection = Input <$ input
  <?> "property_lvar_port_direction"

propertyFormalType :: Parser PropertyFormalType
propertyFormalType
  =   SequenceFormalType_PropertyFormalType <$> sequenceFormalType
  <|> PropertyFormalType <$ property
  <?> "property_formal_type"

propertySpec :: Parser PropertySpec
propertySpec = PropertySpec
  <$> optional clockingEvent
  <*> optional (disable *> iff *> between lparen rparen (expressionOrDist))
  <*> propertyExpr
  <?> "property_spec"

propertyExpr :: Parser PropertyExpr
propertyExpr
  =   SequenceExpr_PropertyExpr
      <$> sequenceExpr
  <|> StrongSequenceExpr_PropertyExpr
      <$> (strong *> between lparen rparen sequenceExpr)
  <|> WeakSequenceExpr_PropertyExpr
      <$> (weak *> between lparen rparen sequenceExpr)
  <|> PropertyExpr
      <$> between lparen rparen propertyExpr
  <|> NotPropertyExpr
      <$> (not_ *> propertyExpr)
  <|> OrPropertyExpr
      <$> propertyExpr
      <*> (or_ *> propertyExpr)
  <|> AndPropertyExpr
      <$> propertyExpr
      <*> (and_ *> propertyExpr)
  <|> ImplicationOverlappedPropertyExpr
      <$> sequenceExpr
      <*> (implication_overlapped *> propertyExpr)
  <|> ImplicationPropertyExpr
      <$> sequenceExpr
      <*> (implication *> propertyExpr)
  <|> IfElsePropertyExpr
      <$> (if_ *> between lparen rparen expressionOrDist)
      <*> propertyExpr
      <*> optional (else_ *> propertyExpr)
  <|> CasePropertyExpr
      <$> (case_ *> between lparen rparen expressionOrDist)
      <*> many1 propertyCaseItem
      <*  endcase
  <|> FollowedByOverlappedPropertyExpr
      <$> sequenceExpr
      <*> (followed_by_overlapped *> propertyExpr)
  <|> FollowedByPropertyExpr
      <$> sequenceExpr
      <*> (followed_by *> propertyExpr)
  <|> NexttimePropertyExpr
      <$> (nexttime *> optional (between lbrack rbrack constantExpression))
      <*> propertyExpr
  <|> SNexttimePropertyExpr
      <$> (s_nexttime *> optional (between lbrack rbrack constantExpression))
      <*> propertyExpr
  <|> AlwaysPropertyExpr
      <$> (always *> optional (between lbrack rbrack cycleDelayConstRangeExpression))
      <*> propertyExpr
  <|> SAlwaysPropertyExpr
      <$> (s_always *> between lbrack rbrack constantRange)
      <*> propertyExpr
  <|> EventuallyPropertyExpr
      <$> (eventually *> between lbrack rbrack constantRange)
      <*> propertyExpr
  <|> SEventuallyPropertyExpr
      <$> (s_eventually *> optional (between lbrack rbrack cycleDelayConstRangeExpression))
      <*> propertyExpr
  <|> UntilPropertyExpr
      <$> propertyExpr
      <*> (until_ *> propertyExpr)
  <|> SUntilPropertyExpr
      <$> propertyExpr
      <*> (s_until *> propertyExpr)
  <|> UntilWithPropertyExpr
      <$> propertyExpr
      <*> (until_with *> propertyExpr)
  <|> SUntilWithPropertyExpr
      <$> propertyExpr
      <*> (s_until_with *> propertyExpr)
  <|> ImpliesPropertyExpr
      <$> propertyExpr
      <*> (implies *> propertyExpr)
  <|> IffPropertyExpr
      <$> propertyExpr
      <*> (iff *> propertyExpr)
  <|> AcceptOnPropertyExpr
      <$> (accept_on *> between lparen rparen expressionOrDist)
      <*> propertyExpr
  <|> RejectOnPropertyExpr
      <$> (reject_on *> between lparen rparen expressionOrDist)
      <*> propertyExpr
  <|> SyncAcceptOnPropertyExpr
      <$> (sync_reject_on *> between lparen rparen expressionOrDist)
      <*> propertyExpr
  <|> SyncRejectOnPropertyExpr
      <$> (sync_reject_on *> between lparen rparen expressionOrDist)
      <*> propertyExpr
  <|> PropertyInstance_PropertyExpr
      <$> propertyInstance
  <|> ClockingEventPropertyExpr
      <$> clockingEvent
      <*> propertyExpr
  <?> "property_expr"

propertyCaseItem :: Parser PropertyCaseItem
propertyCaseItem
  =   PropertyCaseItem
      <$> (Just <$> many1 expressionOrDist <* colon)
      <*> propertyExpr
      <*  optional semi
  <|> PropertyCaseItem
      <$> (Nothing <$ default_)
      <*> (optional colon *> propertyExpr)
      <*  optional semi
  <?> "property_case_item"

sequenceDeclaration :: Parser SequenceDeclaration
sequenceDeclaration = SequenceDeclaration
  <$> (sequence__ *> sequenceIdentifier)
  <*> (optional (between lparen rparen (optional sequencePortList)) <* semi)
  <*> many assertionVariableDeclaration
  <*> (sequenceExpr <* optional semi)
  <*> (endsequence *> optional (colon *> sequenceIdentifier))
  <?> "sequence_declaration"

sequencePortList :: Parser SequencePortList
sequencePortList = sequencePortItem `sepBy1` comma
  <?> "sequence_port_list"

sequencePortItem :: Parser SequencePortItem
sequencePortItem = SequencePortItem
  <$> many attributeInstance
  <*> optional (local *> optional sequenceLvarPortDirection)
  <*> sequenceFormalType
  <*> formalPortIdentifier
  <*> many variableDimension
  <*> optional (assign_op *> sequenceActualArg)
  <?> "sequence_port_item"

sequenceLvarPortDirection :: Parser SequenceLvarPortDirection
sequenceLvarPortDirection = Input <$ input <|> Inout <$ inout <|> Output <$ output
  <?> "sequence_lvar_port_direction"

sequenceFormalType :: Parser SequenceFormalType
sequenceFormalType
  =   DataTypeOrImplicit_SequenceFormalType <$> dataTypeOrImplicit
  <|> SequenceFormalType <$ sequence__
  <|> UntypedFormalType  <$ untyped
  <?> "sequence_formal_type"

sequenceExpr :: Parser SequenceExpr
sequenceExpr
  =   SequenceExpr
      <$> optional sequenceExpr
      <*> many1 ((,) <$> cycleDelayRange <*> sequenceExpr)
  <|> ExpressionOrDist_SequenceExpr
      <$> expressionOrDist
      <*> optional booleanAbbrev
  <|> SequenceInstance_SequenceExpr
      <$> sequenceInstance
      <*> optional sequenceAbbrev 
  <|> SequenceMatchList_SequenceExpr
      <$> (lparen *> sequenceExpr)
      <*> (optional (comma *> sepBy1 sequenceMatchItem comma) <* rparen)
      <*> optional sequenceAbbrev
  <|> AndSequenceExpr
      <$> sequenceExpr
      <*> (and_ *> sequenceExpr)
  <|> IntersectSequenceExpr
      <$> sequenceExpr
      <*> (intersect *> sequenceExpr)
  <|> OrSequenceExpr
      <$> sequenceExpr
      <*> (or_ *> sequenceExpr)
  <|> FirstMatchSequenceExpr
      <$> (first_match *> lparen *> sequenceExpr)
      <*> (optional (comma *> sepBy1 sequenceMatchItem comma) <* rparen)
  <|> ThroughoutSequenceExpr
      <$> expressionOrDist
      <*> (throughout *> sequenceExpr)
  <|> WithinSequenceExpr
      <$> sequenceExpr
      <*> (within *> sequenceExpr)
  <|> ClockingEventSequenceExpr
      <$> clockingEvent
      <*> sequenceExpr
  <?> "sequence_expr"

cycleDelayRange :: Parser CycleDelayRange
cycleDelayRange
  =   ConstantPrimary_CycleDelayRange
      <$> (doublehash *> constantPrimary)
  <|> CycleDelayConstRangeExpression_CycleDelayRange
      <$> (doublehash *> cycleDelayConstRangeExpression)
  <|> PlusCycleDelayRange
      <$  (doublehash *> between rbrack lbrack plus)
  <|> StarCycleDelayRange
      <$  (doublehash *> between rbrack lbrack star)
  <?> "cycle_delay_range"

sequenceMethodCall :: Parser SequenceMethodCall
sequenceMethodCall = SequenceMethodCall
  <$> sequenceInstance
  <*> (dot *> methodIdentifier)
  <?> "sequence_method_call"

sequenceMatchItem :: Parser SequenceMatchItem
sequenceMatchItem
  =   OperatorAssignment_SequenceMatchItem <$> operatorAssignment
  <|> IncOrDecExpression_SequenceMatchItem <$> incOrDecExpression
  <|> SubroutineCall_SequenceMatchItem <$> subroutineCall
  <?> "sequence_match_item"

sequenceInstance :: Parser SequenceInstance
sequenceInstance = SequenceInstance
  <$> psOrHierarchicalSequenceIdentifier
  <*> optional (between lparen rparen sequenceListOfArguments)
  <?> "sequence_instance"

sequenceListOfArguments :: Parser SequenceListOfArguments
sequenceListOfArguments
  =   SequenceListOfArguments
      <$> sepBy (optional sequenceActualArg) comma
      <*> optional (comma *> sepBy item comma)
  <|> SequenceListOfArguments
      <$> pure []
      <*> (Just <$> sepBy1 item comma)
  <?> "sequence_list_of_arguments"
  where item = (,) <$> (dot *> identifier) <*> between lparen rparen (optional sequenceActualArg)

sequenceActualArg :: Parser SequenceActualArg
sequenceActualArg
  =   EventExpression_SequenceActualArg <$> eventExpression
  <|> SequenceExpr_SequenceActualArg <$> sequenceExpr
  <?> "sequence_actual_arg"

booleanAbbrev :: Parser BooleanAbbrev
booleanAbbrev
  =   ConsecutiveRepetition_BooleanAbbrev <$> consecutiveRepetition
  <|> NonConsecutiveRepetition_BooleanAbbrev <$> nonConsecutiveRepetition
  <|> GotoRepetition_BooleanAbbrev <$> gotoRepetition
  <?> "boolean_abbrev"

sequenceAbbrev :: Parser SequenceAbbrev
sequenceAbbrev = consecutiveRepetition
  <?> "sequence_abbrev"

consecutiveRepetition :: Parser ConsecutiveRepetition
consecutiveRepetition
  =   ConstOrRangeExpression_ConsecutiveRepetition
      <$> between lbrack rbrack (star *> constOrRangeExpression)
  <|> StarConsecutiveRepetition
      <$ between lbrack rbrack star
  <|> PlusConsecutiveRepetition
      <$ between lbrack rbrack plus 
  <?> "consecutive_repetition"

nonConsecutiveRepetition :: Parser NonConsecutiveRepetition
nonConsecutiveRepetition = NonConsecutiveRepetition
  <$> between lbrack rbrack (assign_op *> constOrRangeExpression)
  <?> "non_consecutive_repetition"

gotoRepetition :: Parser GotoRepetition
gotoRepetition = GotoRepetition
  <$> between lbrack rbrack (arrow *> constOrRangeExpression)
  <?> "goto_repetition"

constOrRangeExpression :: Parser ConstOrRangeExpression
constOrRangeExpression
  =   ConstantExpression_ConstOrRangeExpression <$> constantExpression
  <|> CycleDelayConstRangeExpression_ConstOrRangeExpression <$> cycleDelayConstRangeExpression
  <?> "const_or_range_expression"


cycleDelayConstRangeExpression :: Parser CycleDelayConstRangeExpression
cycleDelayConstRangeExpression = CycleDelayConstRangeExpression
  <$> (constantExpression <* colon)
  <*> (Nothing <$ dollar <|> Just <$> constantExpression)
  <?> "cycle_delay_const_range_expression"

expressionOrDist :: Parser ExpressionOrDist
expressionOrDist = ExpressionOrDist
  <$> expression
  <*> optional (dist *> between lbrace rbrace distList)
  <?> "expression_or_dist"

assertionVariableDeclaration :: Parser AssertionVariableDeclaration
assertionVariableDeclaration = AssertionVariableDeclaration
  <$> varDataType
  <*> listOfVariableDeclAssignments
  <*  semi
  <?> "assertion_variable_declaration"

letDeclaration :: Parser LetDeclaration
letDeclaration = LetDeclaration
  <$> (let_ *> letIdentifier)
  <*> optional (between lparen rparen (optional letPortList))
  <*> (assign_op *> expression)
  <*  semi
  <?> "let_declaration"

letIdentifier :: Parser LetIdentifier
letIdentifier = identifier <?> "let_identifier"

letPortList :: Parser LetPortList
letPortList = letPortItem `sepBy1` comma
  <?> "let_port_list"

letPortItem :: Parser LetPortItem
letPortItem = LetPortItem
  <$> many attributeInstance
  <*> letFormalType
  <*> formalPortIdentifier
  <*> many variableDimension
  <*> optional (assign_op *> expression)
  <?> "let_port_item"

letFormalType :: Parser LetFormalType
letFormalType
  =   DataTypeOrImplicit_LetFormalType <$> dataTypeOrImplicit
  <|> UntypedLetFormalType <$ untyped
  <?> "let_formal_type"

letExpression :: Parser LetExpression
letExpression = LetExpression
  <$> optional packageScope
  <*> letIdentifier
  <*> optional (between lparen rparen (optional letListOfArguments))
  <?> "let_expression"

letListOfArguments :: Parser LetListOfArguments
letListOfArguments
  =   LetListOfArguments
      <$> sepBy (optional letActualArg) comma
      <*> optional (comma *> sepBy item comma)
  <|> LetListOfArguments
      <$> pure []
      <*> (Just <$> sepBy1 item comma)
  <?> "let_list_of_arguments"
  where item = (,) <$> (dot *> identifier) <*> between lparen rparen (optional letActualArg)

letActualArg :: Parser LetActualArg
letActualArg = expression <?> "let_actual_arg"

-- | A.2.11 Covergroup declarations
--
covergroupDeclaration :: Parser CovergroupDeclaration
covergroupDeclaration = CovergroupDeclaration
  <$> (covergroup *> covergroupIdentifier)
  <*> optional (between lparen rparen (optional tfPortList))
  <*> (optional coverageEvent <* semi)
  <*> many coverageSpecOrOption
  <*> (endgroup *> optional (colon *> covergroupIdentifier))
  <?> "covergroup_declaration"

coverageSpecOrOption :: Parser CoverageSpecOrOption
coverageSpecOrOption
  =   CoverageSpec_CoverageSpecOrOption
      <$> many attributeInstance
      <*> coverageSpec
  <|> CoverageOption_CoverageSpecOrOption
      <$> many attributeInstance
      <*> coverageOption
      <*  semi
  <?> "coverage_spec_or_option"

coverageOption :: Parser CoverageOption
coverageOption
  =   CoverageOption
      <$> (option *> dot *> memberIdentifier)
      <*> (assign_op *> expression)
  <|> CoverageTypeOption
      <$> (type_option *> dot *> memberIdentifier)
      <*> (assign_op *> expression)
  <?> "coverage_option"

coverageSpec :: Parser CoverageSpec
coverageSpec
  =   CoverPoint_CoverageSpec <$> coverPoint
  <|> CoverCross_CoverageSpec <$> coverCross
  <?> "coverage_spec"

coverageEvent :: Parser CoverageEvent
coverageEvent
  =   ClockingEvent_CoverageEvent
      <$> clockingEvent
  <|> WithFunctionSample
      <$> (with *> function *> sample *> between lparen rparen (optional tfPortList))
  <|> BlockEventExpression_CoverageEvent
      <$> (doubleat *> between lparen rparen blockEventExpression)
  <?> "coverage_event"

blockEventExpression :: Parser BlockEventExpression
blockEventExpression
  =   OrBlockEventExpression
      <$> blockEventExpression
      <*> (or_ *> blockEventExpression)
  <|> BeginBlockEvent
      <$> (begin *> hierarchicalBtfIdentifier)
  <|> EndBlockEvent
      <$> (end *> hierarchicalBtfIdentifier)
  <?> "block_event_expression"

hierarchicalBtfIdentifier :: Parser HierarchicalBtfIdentifier
hierarchicalBtfIdentifier
  =   HierarchicalTfIdentifier_HierarchicalBtfIdentifier
      <$> hierarchicalTfIdentifier
  <|> HierarchicalBlockIdentifier_HierarchicalBtfIdentifier
      <$> hierarchicalBlockIdentifier
  <|> MethodIdentifier_HierarchicalBtfIdentifier
      <$> optional (Left <$> hierarchicalIdentifier <* dot <|> Right <$> classScope)
      <*> methodIdentifier
  <?> "hierarchical_btf_identifier"

coverPoint :: Parser CoverPoint
coverPoint = CoverPoint
  <$> optional ((,) <$> optional dataTypeOrImplicit <*> coverPointIdentifier <* colon)
  <*> (coverpoint *> expression)
  <*> optional (iff *> between lparen rparen expression)
  <*> binsOrEmpty
  <?> "cover_point"

binsOrEmpty :: Parser BinsOrEmpty
binsOrEmpty
  =   Just <$> between lbrace rbrace ((,) <$> many attributeInstance <*> sepBy binsOrOptions semi)
  <|> Nothing <$ semi
  <?> "bins_or_empty"

binsOrOptions :: Parser BinsOrOptions
binsOrOptions
  =   CoverageOption_BinsOrOptions
      <$> coverageOption
  <|> CovergroupRangeList_BinsOrOptions
      <$> optional wildcard
      <*> binsKeyword
      <*> binIdentifier
      <*> optional (between lbrack rbrack (optional covergroupExpression))
      <*> (assign_op *> between lbrace rbrace covergroupRangeList)
      <*> optional (with *> between lparen rparen withCovergroupExpression)
      <*> optional (iff *> between lparen rparen expression)
  <|> CoverPointIdentifier_BinsOrOptions
      <$> optional wildcard
      <*> binsKeyword
      <*> binIdentifier
      <*> optional (between lbrack rbrack (optional covergroupExpression))
      <*> (assign_op *> coverPointIdentifier)
      <*> optional (with *> between lparen rparen withCovergroupExpression)
      <*> optional (iff *> between lparen rparen expression)
  <|> SetCovergroupExpression_BinsOrOptions
      <$> optional wildcard
      <*> binsKeyword
      <*> binIdentifier
      <*> optional (between lbrack rbrack (optional covergroupExpression))
      <*> (assign_op *> setCovergroupExpression)
      <*> optional (iff *> between lparen rparen expression)
  <|> TransList_BinsOrOptions
      <$> optional wildcard
      <*> binsKeyword
      <*> binIdentifier
      <*> optional (lbrack *> rbrack)
      <*> (assign_op *> transList)
      <*> optional (iff *> between lparen rparen expression)
  <|> DefaultBinsOrOptions
      <$> binsKeyword
      <*> binIdentifier
      <*> (optional (between lbrack rbrack (optional covergroupExpression)) <* assign_op <* default_)
      <*> optional (iff *> between lparen rparen expression)
  <|> DefaultSequenceBinsOrOptions
      <$> binsKeyword
      <*> (binIdentifier <* assign_op <* default_ <* sequence__)
      <*> optional (iff *> between lparen rparen expression)
  <?> "bins_or_options"

binsKeyword :: Parser BinsKeyword
binsKeyword
  =   Bins <$ bins
  <|> IllegalBins <$ illegal_bins
  <|> IgnoreBins  <$ ignore_bins
  <?> "bins_keyword"

transList :: Parser TransList
transList = between lparen rparen transSet `sepBy1` comma
  <?> "trans_list"

transSet :: Parser TransSet
transSet = transRangeList `sepBy1` eq_arrow
  <?> "trans_set"

transRangeList :: Parser TransRangeList
transRangeList
  =   TransItem <$> transItem
  <|> TransItemStar   <$> transItem <*> between lbrack rbrack (star   *> repeatRange)
  <|> TransItemArrow  <$> transItem <*> between lbrack rbrack (arrow  *> repeatRange)
  <|> TransItemAssign <$> transItem <*> between lbrack rbrack (assign_op *> repeatRange)
  <?> "trans_range_list"

transItem :: Parser TransItem
transItem = covergroupRangeList <?> "trans_item"

repeatRange :: Parser RepeatRange
repeatRange = RepeatRange
  <$> covergroupExpression
  <*> optional (colon *> covergroupExpression)
  <?> "repeat_range"

coverCross :: Parser CoverCross
coverCross = CoverCross
  <$> optional (crossIdentifier <* colon)
  <*> (cross *> listOfCrossItems)
  <*> optional (iff *> between lparen rparen expression)
  <*> crossBody
  <?> "cover_cross"

listOfCrossItems :: Parser ListOfCrossItems
listOfCrossItems = (:) <$> (crossItem <* comma) <*> sepBy1 crossItem comma
  <?> "list_of_cross_items"

crossItem :: Parser CrossItem
crossItem
  =   CoverPointIdentifier_CrossItem <$> coverPointIdentifier
  <|> VariableIdentifier_CrossItem <$> variableIdentifier
  <?> "cross_item"

crossBody :: Parser CrossBody
crossBody
  =   between lbrace rbrace (crossBodyItem `sepBy1` semi)
  <|> [] <$ semi
  <?> "cross_body"

crossBodyItem :: Parser CrossBodyItem
crossBodyItem
  =   FunctionDeclaration_CrossBodyItem <$> functionDeclaration
  <|> BinsSelectionOrOption_CrossBodyItem <$> binsSelectionOrOption <* semi
  <?> "cross_body_item"

binsSelectionOrOption :: Parser BinsSelectionOrOption
binsSelectionOrOption
  =   CoverageOption_BinsSelectionOrOption
      <$> many attributeInstance
      <*> coverageOption
  <|> BinsSelection_BinsSelectionOrOption
      <$> many attributeInstance
      <*> binsSelection
  <?> "bins_selection_or_option"

binsSelection :: Parser BinsSelection
binsSelection = BinsSelection
  <$> binsKeyword
  <*> binIdentifier
  <*> (assign_op *> selectExpression)
  <*> optional (iff *> between lparen rparen expression)
  <?> "bins_selection"

selectExpression :: Parser SelectExpression
selectExpression
  =   SelectCondition
      <$> selectCondition
  <|> NotSelectCondition
      <$> (not_op *> selectCondition)
  <|> AndSelectExpression
      <$> selectExpression
      <*> (and_op *> selectExpression)
  <|> OrSelectExpression
      <$> selectExpression
      <*> (or_op *> selectExpression)
  <|> SelectExpression
      <$> between lparen rparen selectExpression
  <|> WithCovergroupExpression
      <$> selectExpression
      <*> (with *> between lparen rparen withCovergroupExpression)
      <*> optional (matches *> integerCovergroupExpression)
  <|> CrossIdentifier_SelectExpression
      <$> crossIdentifier
  <|> CrossSetExpression_SelectExpression
      <$> crossSetExpression
      <*> optional (matches *> integerCovergroupExpression)
  <?> "select_expression"

selectCondition :: Parser SelectCondition
selectCondition = (,)
  <$> (binsof *> between lparen rparen binsExpression)
  <*> optional (intersect *> between lbrace rbrace covergroupRangeList)
  <?> "select_condition"

binsExpression :: Parser BinsExpression
binsExpression
  =   VariableIdentifier_BinsExpression
      <$> variableIdentifier
  <|> CoverpointIdentifier_BinsExpression
      <$> coverPointIdentifier
      <*> optional (dot *> binIdentifier)
  <?> "bins_expression"

covergroupRangeList :: Parser CovergroupRangeList
covergroupRangeList = covergroupValueRange `sepBy1` comma
  <?> "covergroup_range_list"

covergroupValueRange :: Parser CovergroupValueRange
covergroupValueRange
  =   CovergroupValueRange
      <$> covergroupExpression
      <*> pure Nothing
  <|> CovergroupValueRange
      <$> (lbrack *> covergroupExpression <* colon)
      <*> (Just <$> covergroupExpression <* rbrack)
  <?> "covergroup_value_range"

withCovergroupExpression :: Parser WithCovergroupExpression
withCovergroupExpression = covergroupExpression <?> "with_covergroup_expression"

setCovergroupExpression :: Parser SetCovergroupExpression
setCovergroupExpression = covergroupExpression <?> "set_covergroup_expression"

integerCovergroupExpression :: Parser IntegerCovergroupExpression
integerCovergroupExpression = covergroupExpression <?> "integer_covergroup_expression"

crossSetExpression :: Parser CrossSetExpression
crossSetExpression = covergroupExpression <?> "cross_set_expression"

covergroupExpression :: Parser CovergroupExpression
covergroupExpression = expression <?> "covergroup_expression"


-- | A.3 Primitive instances
--
--   A.3.1 Primitive instantiation and instances
--

gateInstantiation :: Parser GateInstantiation
gateInstantiation
  =   CmosSwitchInstanceList_GateInstantiation
      <$> cmosSwitchtype
      <*> optional delay3
      <*> sepBy1 cmosSwitchInstance comma
      <*  semi
  <|> EnableGateInstanceList_GateInstantiation
      <$> enableGatetype
      <*> optional driveStrength
      <*> optional delay3
      <*> sepBy1 enableGateInstance comma
      <*  semi
  <|> MosSwitchInstanceList_GateInstantiation
      <$> mosSwitchtype
      <*> optional delay3
      <*> sepBy1 mosSwitchInstance comma
      <*  semi
  <|> NInputGateInstanceList_GateInstantiation
      <$> nInputGatetype
      <*> optional driveStrength
      <*> optional delay2
      <*> sepBy1 nInputGateInstance comma
      <*  semi
  <|> NOutputGateInstanceList_GateInstantiation
      <$> nOutputGatetype
      <*> optional driveStrength
      <*> optional delay2
      <*> sepBy1 nOutputGateInstance comma
      <*  semi
  <|> PassEnableSwitchInstanceList_GateInstantiation
      <$> passEnSwitchtype
      <*> optional delay2
      <*> sepBy1 passEnableSwitchInstance comma
      <*  semi
  <|> PassSwitchInstanceList_GateInstantiation
      <$> passSwitchtype
      <*> sepBy1 passSwitchInstance comma
      <*  semi
  <|> PulldownGateInstanceList_GateInstantiation
      <$> (pulldown *> optional pulldownStrength)
      <*> sepBy1 pullGateInstance comma
      <*  semi
  <|> PullupGateInstanceList_GateInstantiation
      <$> (pullup *> optional pullupStrength)
      <*> sepBy1 pullGateInstance comma
      <*  semi
  <?> "gate_instantiation"

cmosSwitchInstance :: Parser CmosSwitchInstance
cmosSwitchInstance = CmosSwitchInstance
  <$> optional nameOfInstance
  <*> between lparen rparen
      ((,,,)
        <$> outputTerminal
        <*> (comma *> inputTerminal)
        <*> (comma *> nControlTerminal)
        <*> (comma *> pControlTerminal))
  <?> "cmos_switch_instance"

enableGateInstance :: Parser EnableGateInstance
enableGateInstance = EnableGateInstance
  <$> optional nameOfInstance
  <*> between lparen rparen
      ((,,)
        <$> outputTerminal
        <*> (comma *> inputTerminal)
        <*> (comma *> enableTerminal))
  <?> "enable_gate_instance"

mosSwitchInstance :: Parser MosSwitchInstance
mosSwitchInstance = MosSwitchInstance
  <$> optional nameOfInstance
  <*> between lparen rparen
      ((,,)
        <$> outputTerminal
        <*> (comma *> inputTerminal)
        <*> (comma *> enableTerminal))
  <?> "mos_switch_instance"

nInputGateInstance :: Parser NInputGateInstance
nInputGateInstance = NInputGateInstance
  <$> optional nameOfInstance
  <*> between lparen rparen ((,) <$> outputTerminal <*> (comma *> sepBy1 inputTerminal comma))
  <?> "n_input_gate_instance"

nOutputGateInstance :: Parser NOutputGateInstance
nOutputGateInstance = NOutputGateInstance
  <$> optional nameOfInstance
  <*> between lparen rparen ((,) <$> sepBy1 outputTerminal comma <*> (comma *> inputTerminal))
  <?> "n_output_gate_instance"

passSwitchInstance :: Parser PassSwitchInstance
passSwitchInstance = PassSwitchInstance
  <$> optional nameOfInstance
  <*> between lparen rparen ((,) <$> inoutTerminal <*> (comma *> inoutTerminal))
  <?> "pass_switch_instance"

passEnableSwitchInstance :: Parser PassEnableSwitchInstance
passEnableSwitchInstance = PassEnableSwitchInstance
  <$> optional nameOfInstance
  <*> between lparen rparen
      ((,,)
        <$> inoutTerminal
        <*> (comma *> inoutTerminal)
        <*> (comma *> enableTerminal))
  <?> "pass_enable_switch_instance"

pullGateInstance :: Parser PullGateInstance
pullGateInstance = PullGateInstance
  <$> optional nameOfInstance
  <*> between lparen rparen outputTerminal
  <?> "pull_gate_instance"


-- | A.3.2 Primitive strengths
--

pulldownStrength :: Parser PulldownStrength
pulldownStrength
  =   Strength0_Strength1_PulldownStrength
      <$> (lparen *> strength0)
      <*> (comma  *> strength1)
      <*  rparen
  <|> Strength1_Strength0_PulldownStrength
      <$> (lparen *> strength1)
      <*> (comma  *> strength0)
      <*  rparen
  <|> Strength0_PulldownStrength <$> between lparen rparen strength0
  <?> "pulldown_strength"

pullupStrength :: Parser PullupStrength
pullupStrength
  =   Strength0_Strength1_PullupStrength
      <$> (lparen *> strength0)
      <*> (comma  *> strength1)
      <*  rparen
  <|> Strength1_Strength0_PullupStrength
      <$> (lparen *> strength1)
      <*> (comma  *> strength0)
      <*  rparen
  <|> Strength1_PullupStrength <$> between lparen rparen strength1
  <?> "pullup_strength"


-- | A.3.3 Primitive terminals
--

enableTerminal :: Parser EnableTerminal
enableTerminal = expression <?> "enable_terminal"

inoutTerminal :: Parser InoutTerminal
inoutTerminal = netLvalue <?> "inout_terminal"

inputTerminal :: Parser InputTerminal
inputTerminal = expression <?> "input_terminal"

nControlTerminal :: Parser NControlTerminal
nControlTerminal = expression <?> "n_control_terminal"

outputTerminal :: Parser OutputTerminal
outputTerminal = netLvalue <?> "output_terminal"

pControlTerminal :: Parser PControlTerminal
pControlTerminal = expression <?> "p_control_terminal"


-- | A.3.4 Primitive gate and switch types
--

cmosSwitchtype :: Parser CmosSwitchtype
cmosSwitchtype
  =   Cmos  <$ cmos
  <|> Rcmos <$ rcmos
  <?> "cmos_switchtype"

enableGatetype :: Parser EnableGatetype
enableGatetype
  =   Bufif0 <$ bufif0
  <|> Bufif1 <$ bufif1
  <|> Notif0 <$ notif0
  <|> Notif1 <$ notif1
  <?> "enable_gatetype"

mosSwitchtype :: Parser MosSwitchtype
mosSwitchtype
  =   Nmos <$ nmos
  <|> Pmos <$ pmos
  <|> Rnmos <$ rnmos
  <|> Rpmos <$ rpmos
  <?> "mos_switchtype"

nInputGatetype :: Parser NInputGatetype
nInputGatetype
  =   AndN  <$ and_
  <|> NandN <$ nand
  <|> OrN   <$ or_
  <|> NorN  <$ nor
  <|> XorN  <$ xor
  <|> XnorN <$ xnor
  <?> "n_input_gatetype"

nOutputGatetype :: Parser NOutputGatetype
nOutputGatetype
  =   BufN <$ buf
  <|> NotN <$ not_
  <?> "n_output_gatetype"

passEnSwitchtype :: Parser PassEnSwitchtype
passEnSwitchtype
  =   Tranif0 <$ tranif0
  <|> Tranif1 <$ tranif1
  <|> Rtranif1 <$ rtranif1
  <|> Rtranif0 <$ rtranif0
  <?> "pass_en_switch_type"

passSwitchtype :: Parser PassSwitchtype
passSwitchtype
  =   Tran <$ tran
  <|> Rtran <$ rtran
  <?> "pass_switchtype"


-- | A.4 Instantiations
--
--   A.4.1 Instantiation
--
--   A.4.1.1 Module instantiation
--

moduleInstantiation :: Parser ModuleInstantiation
moduleInstantiation = ModuleInstantiation
  <$> moduleIdentifier
  <*> optional parameterValueAssignment
  <*> sepBy1 hierarchicalInstance comma
  <*  semi
  <?> "module_instantiation"

parameterValueAssignment :: Parser ParameterValueAssignment
parameterValueAssignment = hash *> between lparen rparen (optional listOfParameterAssignments)
  <?> "parameter_value_assignment"

listOfParameterAssignments :: Parser ListOfParameterAssignments
listOfParameterAssignments
  =   Left  <$> sepBy1 orderedParameterAssignment comma
  <|> Right <$> sepBy1 namedParameterAssignment comma
  <?> "list_of_parameter_assignments"

orderedParameterAssignment :: Parser OrderedParameterAssignment
orderedParameterAssignment = paramExpression <?> "ordered_parameter_assignment"

namedParameterAssignment :: Parser NamedParameterAssignment
namedParameterAssignment = (,)
  <$> (dot *> parameterIdentifier)
  <*> between lparen rparen (optional paramExpression)
  <?> "named_parameter_assignment"

hierarchicalInstance :: Parser HierarchicalInstance
hierarchicalInstance = HierarchicalInstance
  <$> nameOfInstance
  <*> between lparen rparen (optional listOfPortConnections)
  <?> "hierarchical_instance"

nameOfInstance :: Parser NameOfInstance
nameOfInstance = (,)
  <$> instanceIdentifier
  <*> many unpackedDimension
  <?> "name_of_instance"

listOfPortConnections :: Parser ListOfPortConnections
listOfPortConnections
  =   Left  <$> sepBy1 orderedPortConnection comma
  <|> Right <$> sepBy1 namedPortConnection comma
  <?> "list_of_port_connections"

orderedPortConnection :: Parser OrderedPortConnection
orderedPortConnection = (,)
  <$> many attributeInstance
  <*> optional expression
  <?> "ordered_port_connection"

namedPortConnection :: Parser NamedPortConnection
namedPortConnection = (,,)
  <$> (many attributeInstance <* dot)
  <*> (Just <$> portIdentifier <|> Nothing <$ star)
  <*> optional (between lparen rparen (optional expression))
  <?> "named_port_connection"

-- | A.4.1.2 Interface instantiation
--
interfaceInstantiation :: Parser InterfaceInstantiation
interfaceInstantiation = InterfaceInstantiation
  <$> interfaceIdentifier
  <*> optional parameterValueAssignment
  <*> sepBy1 hierarchicalInstance comma
  <*  semi
  <?> "interface_instantiation"

-- | A.4.1.3 Program instantiation
--
programInstantiation :: Parser ProgramInstantiation
programInstantiation = ProgramInstantiation
  <$> programIdentifier
  <*> optional parameterValueAssignment
  <*> sepBy1 hierarchicalInstance comma
  <*  semi
  <?> "program_instantiation"

-- | A.4.1.4 Checker instantiation
--
checkerInstantiation :: Parser CheckerInstantiation
checkerInstantiation = CheckerInstantiation
  <$> psCheckerIdentifier
  <*> nameOfInstance
  <*> between lparen rparen (optional listOfCheckerPortConnections)
  <*  semi
  <?> "checker_instantiation"

listOfCheckerPortConnections :: Parser ListOfCheckerPortConnections
listOfCheckerPortConnections
  =   Left  <$> sepBy1 orderedCheckerPortConnection comma
  <|> Right <$> sepBy1 namedCheckerPortConnection comma
  <?> "list_of_checker_port_connections"

orderedCheckerPortConnection :: Parser OrderedCheckerPortConnection
orderedCheckerPortConnection = (,)
  <$> many attributeInstance
  <*> optional propertyActualArg
  <?> "ordered_checker_port_connection"

namedCheckerPortConnection :: Parser NamedCheckerPortConnection
namedCheckerPortConnection = (,,)
  <$> (many attributeInstance <* dot)
  <*> (Just <$> formalPortIdentifier <|> Nothing <$ star)
  <*> optional (between lparen rparen (optional propertyActualArg))
  <?> "named_checker_port_connection"


-- | A.4.2 Generated instantiation
-- 

generateRegion :: Parser GenerateRegion
generateRegion = generate *> many generateItem <* endgenerate
  <?> "generate_region"

loopGenerateConstruct :: Parser LoopGenerateConstruct
loopGenerateConstruct = LoopGenerateConstruct
  <$> (for *> lparen *> genvarInitialization)
  <*> (semi *> genvarExpression)
  <*> (semi *> genvarIteration <* rparen)
  <*> generateBlock
  <?> "loop_generate_construct"

genvarInitialization :: Parser GenvarInitialization
genvarInitialization = GenvarInitialization
  <$> optional genvar
  <*> genvarIdentifier
  <*> (assign_op *> constantExpression)
  <?> "genvar_initialization"

genvarIteration :: Parser GenvarIteration
genvarIteration
  =   GenvarIterationAssignment
      <$> genvarIdentifier
      <*> assignmentOperator
      <*> genvarExpression
  <|> GenvarIterationIncOrDec
      <$> (Left <$> incOrDecOperator)
      <*> genvarIdentifier
  <|> flip GenvarIterationIncOrDec
      <$> genvarIdentifier
      <*> (Right <$> incOrDecOperator)
  <?> "genvar_iteration"

conditionalGenerateConstruct :: Parser ConditionalGenerateConstruct
conditionalGenerateConstruct
  =   IfGenerateConstruct_ConditionalGenerateConstruct <$> ifGenerateConstruct
  <|> CaseGenerateConstruct_ConditionalGenerateConstruct <$> caseGenerateConstruct
  <?> "conditional_generate_construct"

ifGenerateConstruct :: Parser IfGenerateConstruct
ifGenerateConstruct = IfGenerateConstruct
  <$> (if_ *> between lparen rparen constantExpression)
  <*> generateBlock
  <*> optional (else_ *> generateBlock)
  <?> "if_generate_construct"

caseGenerateConstruct :: Parser CaseGenerateConstruct
caseGenerateConstruct = CaseGenerateConstruct
  <$> (case_ *> between lparen rparen constantExpression)
  <*> many1 caseGenerateItem
  <*  endcase
  <?> "case_generate_construct"

caseGenerateItem :: Parser CaseGenerateItem
caseGenerateItem = CaseGenerateItem
  <$> (Just <$> sepBy1 constantExpression comma <* colon <|> Nothing <$ default_ <* optional colon)
  <*> generateBlock
  <?> "case_generate_item"

generateBlock :: Parser GenerateBlock
generateBlock
  =   GenerateItem_GenerateBlock
      <$> generateItem
  <|> GenerateBlock
      <$> optional (generateBlockIdentifier <* colon)
      <*> (begin *> optional (colon *> generateBlockIdentifier))
      <*> (many generateItem <* end)
      <*> optional (colon *> generateBlockIdentifier)
  <?> "generate_block"

generateItem :: Parser GenerateItem
generateItem
  =   ModuleOrGenerateItem_GenerateItem <$> moduleOrGenerateItem
  <|> InterfaceOrGenerateItem_GenerateItem <$> interfaceOrGenerateItem
  <|> CheckerOrGenerateItem_GenerateItem <$> checkerOrGenerateItem
  <?> "generate_item"


-- | A.5 UDP declaration and instantiation
-- 
--   A.5.1 UDP declaration
--

udpNonansiDeclaration :: Parser UdpNonansiDeclaration
udpNonansiDeclaration = UdpNonansiDeclaration
  <$> many attributeInstance
  <*> (primitive *> udpIdentifier)
  <*> between lparen rparen udpPortList
  <*  semi
  <?> "udp_nonansi_declaration"

udpAnsiDeclaration :: Parser UdpAnsiDeclaration
udpAnsiDeclaration = UdpAnsiDeclaration
  <$> many attributeInstance
  <*> (primitive *> udpIdentifier)
  <*> between lparen rparen udpDeclarationPortList
  <*  semi
  <?> "udp_ansi_declaration"

udpDeclaration :: Parser UdpDeclaration
udpDeclaration
  =   UdpNonansiDeclaration_UdpDeclaration
      <$> udpNonansiDeclaration 
      <*> many1 udpPortDeclaration
      <*> (udpBody <* endprimitive)
      <*> optional (colon *> udpIdentifier)
  <|> UdpAnsiDeclaration_UdpDeclaration
      <$> udpAnsiDeclaration
      <*> (udpBody <* endprimitive)
      <*> optional (colon *> udpIdentifier)
  <|> ExternUdpNonansiDeclaration_UdpDeclaration
      <$> (extern *> udpNonansiDeclaration)
  <|> ExternUdpAnsiDeclaration_UdpDeclaration
      <$> (extern *> udpAnsiDeclaration)
  <|> UdpDeclaration
      <$> many attributeInstance
      <*> (primitive *> udpIdentifier <* lparen <* dot <* star <* rparen <* semi)
      <*> many udpPortDeclaration
      <*> (udpBody <* endprimitive)
      <*> optional (colon *> udpIdentifier)
  <?> "udp_declaration"


-- | A.5.2 UDP ports
--

udpPortList :: Parser UdpPortList
udpPortList = (,)
  <$> outputPortIdentifier
  <*> (comma *> sepBy1 inputPortIdentifier comma)
  <?> "udp_port_list"

udpDeclarationPortList :: Parser UdpDeclarationPortList
udpDeclarationPortList = (,)
  <$> udpOutputDeclaration
  <*> (comma *> sepBy1 udpInputDeclaration comma)
  <?> "udp_declaration_port_list"

udpPortDeclaration :: Parser UdpPortDeclaration
udpPortDeclaration
  =   UdpOutputDeclaration_UdpPortDeclaration <$> udpOutputDeclaration <* semi
  <|> UdpInputDeclaration_UdpPortDeclaration <$> udpInputDeclaration <* semi
  <|> UdpRegDeclaration_UdpPortDeclaration <$> udpRegDeclaration <* semi
  <?> "udp_port_declaration"

udpOutputDeclaration :: Parser UdpOutputDeclaration
udpOutputDeclaration
  =   UdpOutput
      <$> many attributeInstance
      <*> (output *> portIdentifier)
  <|> UdpOutputReg
      <$> many attributeInstance
      <*> (output *> reg *> portIdentifier)
      <*> optional (assign_op *> constantExpression)
  <?> "udp_output_declaration"

udpInputDeclaration :: Parser UdpInputDeclaration
udpInputDeclaration = UdpInput
  <$> many attributeInstance
  <*> (input *> listOfUdpPortIdentifiers)
  <?> "udp_input_declaration"

udpRegDeclaration :: Parser UdpRegDeclaration
udpRegDeclaration = UdpReg
  <$> many attributeInstance
  <*> (input *> variableIdentifier)
  <?> "udp_reg_declaration"


-- | A.5.3 UDP body
--

udpBody :: Parser UdpBody
udpBody
  =   CombinationalBody_UdpBody <$> combinationalBody
  <|> SequentialBody_UdpBody <$> sequentialBody
  <?> "udp_body"

combinationalBody :: Parser CombinationalBody
combinationalBody = table *> many1 combinationalEntry <* endtable
  <?> "combinational_body"

combinationalEntry :: Parser CombinationalEntry
combinationalEntry = CombinationalEntry
  <$> levelInputList
  <*> (colon *> outputSymbol)
  <*  semi
  <?> "combinational_entry"

sequentialBody :: Parser SequentialBody
sequentialBody = SequentialBody
  <$> optional udpInitialStatement
  <*> (table *> many1 sequentialEntry)
  <*  endtable
  <?> "sequential_body"

udpInitialStatement :: Parser UdpInitialStatement
udpInitialStatement = UdpInitialStatement
  <$> (initial *> outputPortIdentifier)
  <*> (assign_op *> initVal)
  <*  semi
  <?> "udp_initial_statement"

initVal :: Parser InitVal
initVal = number <?> "init_val"

sequentialEntry :: Parser SequentialEntry
sequentialEntry = SequentialEntry
  <$> seqInputList
  <*> (colon *> currentState)
  <*> (colon *> nextState)
  <*  semi
  <?> "sequential_entry"

seqInputList :: Parser SeqInputList
seqInputList
  =   LevelInputList_SeqInputList <$> levelInputList
  <|> EdgeInputList_SeqInputList <$> edgeInputList
  <?> "seq_input_list"

levelInputList :: Parser LevelInputList
levelInputList = many1 levelSymbol <?> "level_input_list"

edgeInputList :: Parser EdgeInputList
edgeInputList = EdgeInputList
  <$> many levelSymbol
  <*> edgeIndicator
  <*> many levelSymbol
  <?> "edge_input_list"

edgeIndicator :: Parser EdgeIndicator
edgeIndicator
  =   EdgeIndicator
      <$> (lparen *> levelSymbol)
      <*> (levelSymbol <* rparen)
  <|> EdgeSymbol_EdgeIndicator
      <$> edgeSymbol
  <?> "edge_indicator"

currentState :: Parser CurrentState
currentState = levelSymbol <?> "current_state"

nextState :: Parser NextState
nextState = Just <$> outputSymbol <|> Nothing <$ minus <?> "next_state"

outputSymbol :: Parser OutputSymbol
outputSymbol = unsignedNumber <?> "output_symbol"

levelSymbol :: Parser LevelSymbol
levelSymbol = Left <$> number <|> Right <$> identifier <?> "level_symbol"

edgeSymbol :: Parser EdgeSymbol
edgeSymbol = Just <$> identifier <|> Nothing <$ star <?> "edge_symbol"


-- | A.5.4 UDP instantiation
--
udpInstantiation :: Parser UdpInstantiation
udpInstantiation = UdpInstantiation
  <$> udpIdentifier
  <*> optional driveStrength
  <*> optional delay2
  <*> sepBy1 udpInstance comma
  <*  semi
  <?> "udp_instantiation"

udpInstance :: Parser UdpInstance
udpInstance = UdpInstance
  <$> (optional nameOfInstance <* lparen)
  <*> ((,) <$> outputTerminal <*> (comma *> sepBy1 inputTerminal comma) <* rparen)
  <?> "udp_instance"


-- | A.6 Behavioral statements
--
--   A.6.1 Continuous assignment and net alias statements
--

continuousAssign :: Parser ContinuousAssign
continuousAssign
  =   ListOfNetAssignments_ContinuousAssign
      <$> (assign *> optional driveStrength)
      <*> optional delay3
      <*> listOfNetAssignments
      <*  semi
  <|> ListOfVariableAssignments_ContinuousAssign
      <$> (assign *> optional delayControl)
      <*> listOfVariableAssignments
      <*  semi
  <?> "continuous_assign"

listOfNetAssignments :: Parser ListOfNetAssignments
listOfNetAssignments = netAssignment `sepBy1` comma
  <?> "list_of_net_assignments"

listOfVariableAssignments :: Parser ListOfVariableAssignments
listOfVariableAssignments = variableAssignment `sepBy1` comma
  <?> "list_of_variable_assignments"

netAlias :: Parser NetAlias
netAlias = NetAlias
  <$> (alias *> netLvalue)
  <*> (assign_op *> sepBy1 netLvalue assign_op)
  <*  semi
  <?> "net_alias"

netAssignment :: Parser NetAssignment
netAssignment = NetAssignment
  <$> netLvalue
  <*> (assign_op *> expression)
  <?> "net_assignment"


-- | A.6.2 Procedural blocks and assignments
--

initialConstruct :: Parser InitialConstruct
initialConstruct = InitialConstruct
  <$> (initial *> statementOrNull)
  <?> "initial_construct"

alwaysConstruct :: Parser AlwaysConstruct
alwaysConstruct = AlwaysConstruct
  <$> alwaysKeyword
  <*> statement
  <?> "always_construct"

alwaysKeyword :: Parser AlwaysKeyword
alwaysKeyword
  =   Always      <$ always
  <|> AlwaysComb  <$ always_comb
  <|> AlwaysLatch <$ always_latch
  <|> AlwaysFf    <$ always_ff
  <?> "always_keyword"

finalConstruct :: Parser FinalConstruct
finalConstruct = FinalConstruct
  <$> (final *> functionStatement)
  <?> "final_construct"

blockingAssignment :: Parser BlockingAssignment
blockingAssignment
  =   VariableBlockingAssignment
      <$> variableLvalue
      <*> (assign_op *> delayOrEventControl)
      <*> expression
  <|> NonrangeVariableBlockingAssignment
      <$> nonrangeVariableLvalue
      <*> (assign_op *> dynamicArrayNew)
  <|> SelectBlockingAssignment
      <$> (Left <$> implicitClassHandle <* dot <|> Right
          <$> (Left <$> classScope <|> Right <$> packageScope))
      <*> hierarchicalVariableIdentifier
      <*> select
      <*> (assign_op *> classNew)
  <|> OperatorAssignment_BlockingAssignment
      <$> operatorAssignment
  <?> "blocking_assignment"

operatorAssignment :: Parser OperatorAssignment
operatorAssignment = OperatorAssignment
  <$> variableLvalue
  <*> assignmentOperator
  <*> expression
  <?> "operator_assignment"

assignmentOperator :: Parser AssignmentOperator
assignmentOperator
  =   Ass        <$ assign_op
  <|> AssPlus    <$ assign_plus
  <|> AssMinus   <$ assign_minus
  <|> AssStar    <$ assign_star
  <|> AssSlash   <$ assign_slash
  <|> AssPercent <$ assign_percent
  <|> AssAmp     <$ assign_amp
  <|> AssPipe    <$ assign_pipe
  <|> AssCaret   <$ assign_caret
  <|> AssShiftL  <$ assign_shift_l
  <|> AssShiftR  <$ assign_shift_r
  <|> AssShiftLL <$ assign_shift_ll
  <|> AssShiftRR <$ assign_shift_rr
  <?> "assignment_operator"

nonblockingAssignment :: Parser NonblockingAssignment
nonblockingAssignment = NonblockingAssignment
  <$> (variableLvalue <* lteq)
  <*> optional delayOrEventControl
  <*> expression
  <?> "nonblocking_assignment"

proceduralContinuousAssignment :: Parser ProceduralContinuousAssignment
proceduralContinuousAssignment
  =   ProceduralContinuousAssign <$> (assign *> variableAssignment)
  <|> ProceduralContinuousDeassign <$> (deassign *> variableLvalue)
  <|> ProceduralContinuousForceVariable <$> (force *> variableAssignment)
  <|> ProceduralContinuousForceNet <$> (force *> netAssignment)
  <|> ProceduralContinuousReleaseVariable <$> (release *> variableLvalue)
  <|> ProceduralContinuousReleaseNet <$> (release *> netLvalue)
  <?> "procedural_continuous_assignment"

variableAssignment :: Parser VariableAssignment
variableAssignment = VariableAssignment
  <$> variableLvalue
  <*> (assign_op *> expression)
  <?> "variable_assignment"


-- | A.6.3 Parallel and sequential blocks
-- 

actionBlock :: Parser ActionBlock
actionBlock
  =   ElseActionBlock
      <$> optional statement
      <*> (else_ *> statementOrNull)
  <|> StatementOrNull_ActionBlock
      <$> statementOrNull
  <?> "action_block"

seqBlock :: Parser SeqBlock
seqBlock = SeqBlock
  <$> (begin *> optional (colon *> blockIdentifier))
  <*> many blockItemDeclaration
  <*> (many statementOrNull <* end)
  <*> optional (colon *> blockIdentifier)
  <?> "seq_block"

parBlock :: Parser ParBlock
parBlock = ParBlock
  <$> (fork *> optional (colon *> blockIdentifier))
  <*> many blockItemDeclaration
  <*> many statementOrNull
  <*> joinKeyword
  <*> optional (colon *> blockIdentifier)
  <?> "par_block"

joinKeyword :: Parser JoinKeyword
joinKeyword
  =   Join     <$ join_
  <|> JoinAny  <$ join_any
  <|> JoinNone <$ join_none
  <?> "join_keyword"


-- | A.6.4 Statements
--

statementOrNull :: Parser StatementOrNull
statementOrNull
  =   Statement_StatementOrNull <$> statement
  <|> Null_StatementOrNull <$> many attributeInstance <* semi
  <?> "statement_or_null"

statement :: Parser Statement
statement = Statement
  <$> optional (blockIdentifier <* colon)
  <*> many attributeInstance
  <*> statementItem
  <?> "statement"

statementItem :: Parser StatementItem
statementItem
  =   BlockingAssignment_StatementItem <$> blockingAssignment <* semi
  <|> NonblockingAssignment_StatementItem <$> nonblockingAssignment <* semi
  <|> ProceduralContinuousAssignment_StatementItem <$> proceduralContinuousAssignment <* semi
  <|> CaseStatement_StatementItem <$> caseStatement
  <|> ConditionalStatement_StatementItem <$> conditionalStatement
  <|> IncOrDecExpression_StatementItem <$> incOrDecExpression <* semi
  <|> SubroutineCallStatement_StatementItem <$> subroutineCallStatement
  <|> DisableStatement_StatementItem <$> disableStatement
  <|> EventTrigger_StatementItem <$> eventTrigger
  <|> LoopStatement_StatementItem <$> loopStatement
  <|> JumpStatement_StatementItem <$> jumpStatement
  <|> ParBlock_StatementItem <$> parBlock
  <|> ProceduralTimingControlStatement_StatementItem <$> proceduralTimingControlStatement <* semi
  <|> SeqBlock_StatementItem <$> seqBlock
  <|> WaitStatement_StatementItem <$> waitStatement
  <|> ProceduralAssertionStatement_StatementItem <$> proceduralAssertionStatement
  <|> ClockingDrive_StatementItem <$> clockingDrive <* semi
  <|> RandsequenceStatement_StatementItem <$> randsequenceStatement
  <|> RandcaseStatement_StatementItem <$> randcaseStatement
  <|> ExpectPropertyStatement_StatementItem <$> expectPropertyStatement
  <?> "statement_item"

functionStatement :: Parser FunctionStatement
functionStatement = statement <?> "function_statement"

functionStatementOrNull :: Parser FunctionStatementOrNull
functionStatementOrNull
  =   FunctionStatement_FunctionStatementOrNull <$> functionStatement
  <|> Null_FunctionStatementOrNull <$> many attributeInstance <* semi
  <?> "function_statement_or_null"

variableIdentifierList :: Parser VariableIdentifierList
variableIdentifierList = variableIdentifier `sepBy1` comma
  <?> "variable_identifier_list"

-- | A.6.5 Timing control statements
--

proceduralTimingControlStatement :: Parser ProceduralTimingControlStatement
proceduralTimingControlStatement = (,)
  <$> proceduralTimingControl
  <*> statementOrNull
  <?> "procedural_timing_control_statement"

delayOrEventControl :: Parser DelayOrEventControl
delayOrEventControl
  =   DelayControl_DelayOrEventControl
      <$> delayControl
  <|> EventControl_DelayOrEventControl
      <$> eventControl
  <|> RepeatEventControl_DelayOrEventControl
      <$> (repeat_ *> between lparen rparen expression)
      <*> eventControl
  <?> "delay_or_event_control"

delayControl :: Parser DelayControl
delayControl
  =   Left  <$> (hash *> delayValue)
  <|> Right <$> (hash *> between lparen rparen mintypmaxExpression)
  <?> "delay_control"

eventControl :: Parser EventControl
eventControl
  =   HierarchicalEventIdentifier_EventControl <$> (at *> hierarchicalEventIdentifier)
  <|> EventExpression_EventControl <$> (at *> between lparen rparen eventExpression)
  <|> EventControl <$ at <* star
  <|> EventControl <$ at <* between lparen rparen star
  <|> PsOrHierarchicalSequenceIdentifier_EventControl <$> psOrHierarchicalSequenceIdentifier
  <?> "event_control"

eventExpression :: Parser EventExpression
eventExpression
  =   Expression_EventExpression
      <$> optional edgeIdentifier
      <*> expression
      <*> optional (iff *> expression)
  <|> SequenceInstance_EventExpression
      <$> sequenceInstance
      <*> optional (iff *> expression)
  <|> OrEventExpression
      <$> eventExpression
      <*> (or_ *> eventExpression)
  <|> SepEventExpression
      <$> eventExpression
      <*> (comma *> eventExpression)
  <|> EventExpression
      <$> between lparen rparen eventExpression
  <?> "event_expression"

proceduralTimingControl :: Parser ProceduralTimingControl
proceduralTimingControl
  =   DelayControl_ProceduralTimingControl <$> delayControl
  <|> EventControl_ProceduralTimingControl <$> eventControl
  <|> CycleDelay_ProceduralTimingControl <$> cycleDelay
  <?> "procedural_timing_control"

jumpStatement :: Parser JumpStatement
jumpStatement
  =   Return <$> optional expression <* semi
  <|> Break <$ break_ <* semi
  <|> Continue <$ continue <* semi
  <?> "jump_statement"

waitStatement :: Parser WaitStatement
waitStatement
  =   Wait
      <$> (wait *> between lparen rparen expression)
      <*> statementOrNull
  <|> WaitFork <$ wait <* fork <* semi
  <|> WaitOrder
      <$> (wait_order *> between lparen rparen (hierarchicalIdentifier `sepBy1` comma))
      <*> actionBlock
  <?> "wait_statement"

eventTrigger :: Parser EventTrigger
eventTrigger
  =   ArrowEventTrigger
      <$> (arrow *> hierarchicalEventIdentifier)
      <*  semi
  <|> DoubleArrowEventTrigger
      <$> (double_arrow *> optional delayOrEventControl)
      <*> hierarchicalEventIdentifier
      <*  semi
  <?> "event_trigger"

disableStatement :: Parser DisableStatement
disableStatement
  =   DisableTask
      <$> (disable *> hierarchicalTaskIdentifier)
      <*  semi
  <|> DisableBlock
      <$> (disable *> hierarchicalBlockIdentifier)
      <*  semi
  <|> DisableFork <$ disable <* fork <* semi
  <?> "disable_statement"


-- | A.6.6 Conditional statements
--

conditionalStatement :: Parser ConditionalStatement
conditionalStatement = ConditionalStatement
  <$> optional uniquePriority
  <*> (if_ *> between lparen rparen condPredicate)
  <*> statementOrNull
  <*> many (else_ >> if_ >> (,) <$> between lparen rparen condPredicate <*> statementOrNull)
  <*> optional (else_ *> statementOrNull)
  <?> "conditional_statement"

uniquePriority :: Parser UniquePriority
uniquePriority
  =   Unique   <$ unique
  <|> Unique0  <$ unique0
  <|> Priority <$ priority
  <?> "unique_priority"

condPredicate :: Parser CondPredicate
condPredicate = CondPredicate
  <$> (sepBy1 expressionOrCondPattern triple_amp)
  <?> "cond_predicate"

expressionOrCondPattern :: Parser ExpressionOrCondPattern
expressionOrCondPattern
  =   Left  <$> expression
  <|> Right <$> condPattern
  <?> "expression_or_cond_pattern"

condPattern :: Parser CondPattern
condPattern = CondPattern
  <$> expression
  <*> (matches *> pattern)
  <?> "cond_pattern"

-- | A.6.7 Case statements
--

caseStatement :: Parser CaseStatement
caseStatement
  =   CaseStatement
      <$> optional uniquePriority
      <*> caseKeyword
      <*> between lparen rparen caseExpression
      <*> many1 caseItem
      <*  endcase
  <|> CaseStatementMatches
      <$> optional uniquePriority
      <*> caseKeyword
      <*> between lparen rparen caseExpression
      <*> (matches *> many1 casePatternItem)
      <*  endcase
  <|> CaseStatementInside
      <$> optional uniquePriority
      <*> (case_ *> between lparen rparen caseExpression)
      <*> (inside *> many1 caseInsideItem)
      <*  endcase
  <?> "case_statement"

caseKeyword :: Parser CaseKeyword
caseKeyword
  =   Case  <$ case_
  <|> Casez <$ casez
  <|> Casex <$ casex
  <?> "case_keyword"

caseExpression :: Parser CaseExpression
caseExpression = expression <?> "case_expression"

caseItem :: Parser CaseItem
caseItem
  =   CaseItem
      <$> (Just <$> sepBy1 caseItemExpression comma <* colon)
      <*> statementOrNull
  <|> CaseItem
      <$> (Nothing <$ default_ <* optional colon)
      <*> statementOrNull
  <?> "case_item"

casePatternItem :: Parser CasePatternItem
casePatternItem
  =   CasePatternItem
      <$> (Just <$> pattern)
      <*> optional expression
      <*> statementOrNull
  <|> CasePatternItem
      <$> (Nothing <$ default_)
      <*> (Nothing <$ optional colon)
      <*> statementOrNull
  <?> "case_pattern_item"

caseInsideItem :: Parser CaseInsideItem
caseInsideItem
  =   CaseInsideItem
      <$> (Just <$> openRangeList)
      <*> statementOrNull
  <|> CaseInsideItem
      <$> (Nothing <$ default_)
      <*> (optional colon *> statementOrNull)
  <?> "case_inside_item"

caseItemExpression :: Parser CaseItemExpression
caseItemExpression = expression <?> "case_item_expression"

randcaseStatement :: Parser RandcaseStatement
randcaseStatement = RandcaseStatement
  <$> (randcase *> many1 randcaseItem)
  <*  endcase
  <?> "randcase_statement"

randcaseItem :: Parser RandcaseItem
randcaseItem = (,)
  <$> expression
  <*> (colon *> statementOrNull)
  <?> "randcase_item"

openRangeList :: Parser OpenRangeList
openRangeList = openValueRange `sepBy1` comma
  <?> "open_range_list"

openValueRange :: Parser OpenValueRange
openValueRange = valueRange <?> "open_value_range"


-- | A.6.7.1 Patterns
--
pattern :: Parser Pattern
pattern
  =   VariableIdentifier_Pattern
      <$> (dot *> variableIdentifier)
  <|> WildcardPattern <$ dot <* star
  <|> ConstantExpression_Pattern
      <$> constantExpression
  <|> TaggedPattern
      <$> (tagged *> memberIdentifier)
      <*> optional pattern
  <|> PatternList_Pattern
      <$> (apostrophe *> between lbrace rbrace (pattern `sepBy1` comma))
  <|> MemberList_Pattern
      <$> (apostrophe *> between lbrace rbrace
            ((,) <$> memberIdentifier <*> (colon *> pattern)) `sepBy1` comma)
  <?> "pattern"
  

assignmentPattern :: Parser AssignmentPattern
assignmentPattern
  =   ExpressionList_AssignmentPattern
      <$> (apostrophe *> between lbrace rbrace (expression `sepBy1` comma))
  <|> StructurePatternKeyList_AssignmentPattern
      <$> (apostrophe *> between lbrace rbrace
            ((,) <$> structurePatternKey <*> (colon *> expression)) `sepBy1` comma)
  <|> ArrayPatternKeyList_AssignmentPattern
      <$> (apostrophe *> between lbrace rbrace
            ((,) <$> arrayPatternKey <*> (colon *> expression)) `sepBy1` comma)
  <|> ConstantExpression_AssignmentPattern
      <$> (apostrophe *> lbrace *> constantExpression)
      <*> between lbrace rbrace (expression `sepBy1` comma)
      <*  rbrace
  <?> "assignment_pattern"

structurePatternKey :: Parser StructurePatternKey
structurePatternKey
  =   Left  <$> memberIdentifier
  <|> Right <$> assignmentPatternKey
  <?> "structure_pattern_key"

arrayPatternKey :: Parser ArrayPatternKey
arrayPatternKey
  =   Left  <$> constantExpression
  <|> Right <$> assignmentPatternKey
  <?> "array_pattern_key"

assignmentPatternKey :: Parser AssignmentPatternKey
assignmentPatternKey = Just <$> simpleType <|> Nothing <$ default_
  <?> "assignment_pattern_key"

assignmentPatternExpression :: Parser AssignmentPatternExpression
assignmentPatternExpression = AssignmentPatternExpression
  <$> optional assignmentPatternExpressionType
  <*> assignmentPattern
  <?> "assignment_pattern_expression"

assignmentPatternExpressionType :: Parser AssignmentPatternExpressionType
assignmentPatternExpressionType
  =   PsTypeIdentifier_AssignmentPatternExpressionType <$> psTypeIdentifier
  <|> PsParameterIdentifier_AssignmentPatternExpressionType <$> psParameterIdentifier
  <|> IntegerAtomType_AssignmentPatternExpressionType <$> integerAtomType
  <|> TypeReference_AssignmentPatternExpressionType <$> typeReference
  <?> "assignment_pattern_expression_type"

constantAssignmentPatternExpression :: Parser ConstantAssignmentPatternExpression
constantAssignmentPatternExpression = assignmentPatternExpression
  <?> "constant_assignment_pattern_expression"

assignmentPatternNetLvalue :: Parser AssignmentPatternNetLvalue
assignmentPatternNetLvalue = apostrophe *> between lbrack rbrack (netLvalue `sepBy1` comma)
  <?> "assignment_pattern_net_lvalue"

assignmentPatternVariableLvalue :: Parser AssignmentPatternVariableLvalue
assignmentPatternVariableLvalue = apostrophe *> between lbrack rbrack (variableLvalue `sepBy1` comma)
  <?> "assignment_pattern_variable_lvalue"


-- | A.6.8 Looping statements
--

loopStatement :: Parser LoopStatement
loopStatement
  =   Forever
      <$> (forever_ *> statementOrNull)
  <|> Repeat
      <$> (repeat_ *> between lparen rparen expression)
      <*> statementOrNull
  <|> While
      <$> (while_ *> between lparen rparen expression)
      <*> statementOrNull
  <|> For
      <$> (lparen *> optional forInitialization)
      <*> (semi *> optional expression)
      <*> (semi *> optional forStep)
      <*> (rparen *> statementOrNull)
  <|> DoWhile
      <$> (do_ *> statementOrNull)
      <*> (while_ *> between lparen rparen expression)
      <*  semi
  <|> Foreach
      <$> (lparen *> psOrHierarchicalArrayIdentifier)
      <*> between lbrack rbrack loopVariables
      <*> (rparen *> statement)
  <?> "loop_statement"

forInitialization :: Parser ForInitialization
forInitialization
  =   Left  <$> listOfVariableAssignments
  <|> Right <$> sepBy1 forVariableDeclaration comma
  <?> "for_initialization"

forVariableDeclaration :: Parser ForVariableDeclaration
forVariableDeclaration = ForVariableDeclaration
  <$> optional var
  <*> dataType
  <*> sepBy1 ((,) <$> variableIdentifier <*> (assign_op *> expression)) comma
  <?> "for_variable_declaration"

forStep :: Parser ForStep
forStep = forStepAssignment `sepBy1` comma
  <?> "for_step"

forStepAssignment :: Parser ForStepAssignment
forStepAssignment
  =   OperatorAssignment_ForStepAssignment <$> operatorAssignment
  <|> IncOrDecExpression_ForStepAssignment <$> incOrDecExpression
  <|> FunctionSubroutineCall_ForStepAssignment <$> functionSubroutineCall
  <?> "for_step_assignment"

loopVariables :: Parser LoopVariables
loopVariables = optional indexVariableIdentifier `sepBy1` comma
  <?> "loop_variables"


-- | A.6.9 Subroutine call statements
--
subroutineCallStatement :: Parser SubroutineCallStatement
subroutineCallStatement
  =   Left  <$> subroutineCall <* semi
  <|> Right <$> (void_ *> apostrophe *> between lparen rparen functionSubroutineCall) <* semi
  <?> "subroutine_call_statement"


-- | A.6.10 Assertion statements
--

assertionItem :: Parser AssertionItem
assertionItem
  =   ConcurrentAssertionItem_AssertionItem <$> concurrentAssertionItem
  <|> DeferredImmediateAssertionItem_AssertionItem <$> deferredImmediateAssertionItem
  <?> "assertion_item"

deferredImmediateAssertionItem :: Parser DeferredImmediateAssertionItem
deferredImmediateAssertionItem = DeferredImmediateAssertionItem
  <$> optional (blockIdentifier <* colon)
  <*> deferredImmediateAssertionStatement
  <?> "deferred_immediate_assertion_item"

proceduralAssertionStatement :: Parser ProceduralAssertionStatement
proceduralAssertionStatement
  =   ConcurrentAssertionStatement_ProceduralAssertionStatement <$> concurrentAssertionStatement
  <|> ImmediateAssertionStatement_ProceduralAssertionStatement <$> immediateAssertionStatement
  <|> CheckerInstantiation_ProceduralAssertionStatement <$> checkerInstantiation
  <?> "procedural_assertion_statement" 

immediateAssertionStatement :: Parser ImmediateAssertionStatement
immediateAssertionStatement
  =   SimpleImmediateAssertionStatement_ImmediateAssertionStatement
      <$> simpleImmediateAssertionStatement
  <|> DeferredImmediateAssertionStatement_ImmediateAssertionStatement
      <$> deferredImmediateAssertionStatement
  <?> "immediate_assertion_statement"

simpleImmediateAssertionStatement :: Parser SimpleImmediateAssertionStatement
simpleImmediateAssertionStatement
  =   SimpleImmediateAssertStatement_SimpleImmediateAssertionStatement
      <$> simpleImmediateAssertStatement
  <|> SimpleImmediateAssumeStatement_SimpleImmediateAssertionStatement
      <$> simpleImmediateAssumeStatement
  <|> SimpleImmediateCoverStatement_SimpleImmediateAssertionStatement
      <$> simpleImmediateCoverStatement
  <?> "simple_immediate_assertion_statement"

simpleImmediateAssertStatement :: Parser SimpleImmediateAssertStatement
simpleImmediateAssertStatement = SimpleImmediateAssertStatement
  <$> (assert *> between lparen rparen expression)
  <*> actionBlock
  <?> "simple_immediate_assert_statement"

simpleImmediateAssumeStatement :: Parser SimpleImmediateAssumeStatement
simpleImmediateAssumeStatement = SimpleImmediateAssumeStatement
  <$> (assume *> between lparen rparen expression)
  <*> actionBlock
  <?> "simple_immediate_assume_statement"

simpleImmediateCoverStatement :: Parser SimpleImmediateCoverStatement
simpleImmediateCoverStatement = SimpleImmediateCoverStatement
  <$> (cover *> between lparen rparen expression)
  <*> statementOrNull
  <?> "simple_immediate_cover_statement"

deferredImmediateAssertionStatement :: Parser DeferredImmediateAssertionStatement
deferredImmediateAssertionStatement
  =   DeferredImmediateAssertStatement_DeferredImmediateAssertionStatement
      <$> deferredImmediateAssertStatement
  <|> DeferredImmediateAssumeStatement_DeferredImmediateAssertionStatement
      <$> deferredImmediateAssumeStatement
  <|> DeferredImmediateCoverStatement_DeferredImmediateAssertionStatement
      <$> deferredImmediateCoverStatement
  <?> "deferred_immediate_assertion_statement"

deferredImmediateAssertStatement :: Parser DeferredImmediateAssertStatement
deferredImmediateAssertStatement = DeferredImmediateAssertStatement
  <$> (assert *> (Final <$ final <|> Zero <$ hash <* unsignedNumber))
  <*> between lparen rparen expression
  <*> actionBlock
  <?> "deferred_immediate_assert_statement"

deferredImmediateAssumeStatement :: Parser DeferredImmediateAssumeStatement
deferredImmediateAssumeStatement = DeferredImmediateAssumeStatement
  <$> (assume *> (Final <$ final <|> Zero <$ hash <* unsignedNumber))
  <*> between lparen rparen expression
  <*> actionBlock
  <?> "deferred_immediate_assume_statement"

deferredImmediateCoverStatement :: Parser DeferredImmediateCoverStatement
deferredImmediateCoverStatement = DeferredImmediateCoverStatement
  <$> (cover *> (Final <$ final <|> Zero <$ hash <* unsignedNumber))
  <*> between lparen rparen expression
  <*> statementOrNull
  <?> "deferred_immediate_cover_statement"


-- | A.6.11 Clocking block
--

clockingDeclaration :: Parser ClockingDeclaration
clockingDeclaration = ClockingDeclaration
  <$> optional default_
  <*> (clocking_ *> optional clockingIdentifier)
  <*> (clockingEvent <* semi)
  <*> many clockingItem
  <*> optional (colon *> clockingIdentifier)
  <?> "clocking_declaration"

clockingEvent :: Parser ClockingEvent
clockingEvent
  =   Identifier_ClockingEvent
      <$> (at *> identifier)
  <|> EventExpression_ClockingEvent
      <$> (at *> between lparen rparen eventExpression)
  <?> "clocking_event"

clockingItem :: Parser ClockingItem
clockingItem
  =   DefaultSkew_ClockingItem
      <$> (default_ *> defaultSkew)
      <*  semi
  <|> ListOfClockingDeclAssign_ClockingItem
      <$> clockingDirection
      <*> listOfClockingDeclAssign
      <*  semi
  <|> AssertionItemDeclaration_ClockingItem
      <$> many attributeInstance
      <*> assertionItemDeclaration
  <?> "clocking_item"

defaultSkew :: Parser DefaultSkew
defaultSkew
  =   InputDefaultSkew <$> (input *> clockingSkew)
  <|> OutputDefaultSkew <$> (output *> clockingSkew)
  <|> InputOutputDefaultSkew <$> (input *> clockingSkew) <*> (output *> clockingSkew)
  <?> "default_skew"

clockingDirection :: Parser ClockingDirection
clockingDirection
  =   InputClockingDirection
      <$> (input  *> optional clockingSkew)
  <|> OutputClockingDirection
      <$> (output *> optional clockingSkew)
  <|> InputOutputClockingDirection
      <$> (input  *> optional clockingSkew)
      <*> (output *> optional clockingSkew)
  <|> InoutClockingDirection <$ inout
  <?> "clocking_direction"

listOfClockingDeclAssign :: Parser ListOfClockingDeclAssign
listOfClockingDeclAssign = clockingDeclAssign `sepBy1` comma
  <?> "list_of_clocking_decl_assign"

clockingDeclAssign :: Parser ClockingDeclAssign
clockingDeclAssign = ClockingDeclAssign
  <$> signalIdentifier
  <*> optional (assign_op *> expression)
  <?> "clocking_decl_assign"

clockingSkew :: Parser ClockingSkew
clockingSkew
  =   EdgeIdentifier_ClockingSkew
      <$> edgeIdentifier
      <*> optional delayControl
  <|> DelayControl_ClockingSkew
      <$> delayControl
  <?> "clocking_skew"

clockingDrive :: Parser ClockingDrive
clockingDrive = ClockingDrive
  <$> clockvarExpression
  <*> (lteq *> optional cycleDelay)
  <*> expression
  <?> "clocking_drive"

cycleDelay :: Parser CycleDelay
cycleDelay
  =   IntegralNumber_CycleDelay <$> (doublehash *> integralNumber)
  <|> Identifier_CycleDelay <$> (doublehash *> identifier)
  <|> Expression_CycleDelay <$> (doublehash *> between lparen rparen expression)
  <?> "cycle_delay"

clockvar :: Parser Clockvar
clockvar = hierarchicalIdentifier <?> "clockvar"

clockvarExpression :: Parser ClockvarExpression
clockvarExpression = (,)
  <$> clockvar
  <*> select
  <?> "clockvar_expression"


-- | A.6.12 Randsequence
--

randsequenceStatement :: Parser RandsequenceStatement
randsequenceStatement = RandsequenceStatement
  <$> (randsequence *> between lparen rparen (optional productionIdentifier))
  <*> many1 production
  <*  endsequence
  <?> "randsequence_statement"

production :: Parser Production
production = Production
  <$> optional dataTypeOrVoid
  <*> productionIdentifier
  <*> optional (between lparen rparen tfPortList)
  <*> (colon *> sepBy1 rsRule pipe)
  <*  semi
  <?> "production"

rsRule :: Parser RsRule
rsRule = RsRule
  <$> rsProductionList
  <*> optional (dweq >> (,) <$> weightSpecification <*> optional rsCodeBlock)
  <?> "rs_rule"

rsProductionList :: Parser RsProductionList
rsProductionList
  =   RsProds_RsProductionList
      <$> many1 rsProd
  <|> ProductionItems_RsProductionList
      <$> (rand *> join_ *> optional (between lparen rparen expression))
      <*> productionItem
      <*> many1 productionItem
  <?> "rs_production_list"

weightSpecification :: Parser WeightSpecification
weightSpecification
  =   IntegralNumber_WeightSpecification <$> integralNumber
  <|> PsIdentifier_WeightSpecification <$> psIdentifier
  <|> Expression_WeightSpecification <$> between lparen rparen expression
  <?> "weight_specification"

rsCodeBlock :: Parser RsCodeBlock
rsCodeBlock = RsCodeBlock
  <$> (lbrack *> many dataDeclaration)
  <*> (many statementOrNull <* rbrack)
  <?> "rs_code_block"

rsProd :: Parser RsProd
rsProd
  =   ProductionItem_RsProd <$> productionItem
  <|> RsCodeBlock_RsProd <$> rsCodeBlock
  <|> RsIfElse_RsProd <$> rsIfElse
  <|> RsRepeat_RsProd <$> rsRepeat
  <|> RsCase_RsProd <$> rsCase
  <?> "rs_prod"

productionItem :: Parser ProductionItem
productionItem = ProductionItem
  <$> productionIdentifier
  <*> optional (between lparen rparen listOfArguments)
  <?> "production_item"

rsIfElse :: Parser RsIfElse
rsIfElse = RsIfElse
  <$> (if_ *> between lparen rparen expression)
  <*> productionItem
  <*> optional (else_ *> productionItem)
  <?> "rs_if_else"

rsRepeat :: Parser RsRepeat
rsRepeat = RsRepeat
  <$> (repeat_ *> between lparen rparen expression)
  <*> productionItem
  <?> "rs_repeat"

rsCase :: Parser RsCase
rsCase = RsCase
  <$> (case_ *> between lparen rparen caseExpression)
  <*> many1 rsCaseItem
  <*  endcase
  <?> "rs_case"

rsCaseItem :: Parser RsCaseItem
rsCaseItem
  =   RsCaseItem
      <$> (Just <$> sepBy1 caseItemExpression comma <* colon)
      <*> productionItem
      <*  semi
  <|> RsCaseItem
      <$> (Nothing <$ default_ <* optional colon)
      <*> productionItem
      <*  semi
  <?> "rs_case_item"


-- | A.7 Specify section
-- 
--   A.7.1 Specify block declaration
--

specifyBlock :: Parser SpecifyBlock
specifyBlock = SpecifyBlock
  <$> (specify *> many specifyItem)
  <*  endspecify
  <?> "specify_block"

specifyItem :: Parser SpecifyItem
specifyItem
  =   SpecparamDeclaration_SpecifyItem <$> specparamDeclaration
  <|> PulsestyleDeclaration_SpecifyItem <$> pulsestyleDeclaration
  <|> ShowcancelledDeclaration_SpecifyItem <$> showcancelledDeclaration
  <|> PathDeclaration_SpecifyItem <$> pathDeclaration
  <|> SystemTimingCheck_SpecifyItem <$> systemTimingCheck
  <?> "specify_item"

pulsestyleDeclaration :: Parser PulsestyleDeclaration
pulsestyleDeclaration
  =   PulsestyleOnevent
      <$> (pulsestyle_onevent *> listOfPathOutputs)
      <*  semi
  <|> PulsestyleOndetect
      <$> (pulsestyle_ondetect *> listOfPathOutputs)
      <*  semi
  <?> "pulsestyle_declaration"

showcancelledDeclaration :: Parser ShowcancelledDeclaration
showcancelledDeclaration
  =   Showcancelled
      <$> (showcancelled *> listOfPathOutputs)
      <*  semi
  <|> Noshowcancelled
      <$> (noshowcancelled *> listOfPathOutputs)
      <*  semi
  <?> "showcancelled_declaration"


-- | A.7.2 Specify path declarations
--

pathDeclaration :: Parser PathDeclaration
pathDeclaration
  =   SimplePathDeclaration_PathDeclaration
      <$> simplePathDeclaration
      <*  semi
  <|> EdgeSensitivePathDeclaration_PathDeclaration
      <$> edgeSensitivePathDeclaration
      <*  semi
  <|> StateDependentPathDeclaration_PathDeclaration
      <$> stateDependentPathDeclaration
      <*  semi
  <?> "path_declaration"

simplePathDeclaration :: Parser SimplePathDeclaration
simplePathDeclaration
  =   ParallelPathDescription_SimplePathDeclaration
      <$> parallelPathDescription
      <*> (assign_op *> pathDelayValue)
  <|> FullPathDescription_SimplePathDeclaration
      <$> fullPathDescription
      <*> (assign_op *> pathDelayValue)
  <?> "simple_path_declaration"

parallelPathDescription :: Parser ParallelPathDescription
parallelPathDescription = ParallelPathDescription
  <$> (lparen *> specifyInputTerminalDescriptor)
  <*> optional polarityOperator
  <*> (eq_arrow *> specifyOutputTerminalDescriptor)
  <*  rparen
  <?> "parallel_path_description"

fullPathDescription :: Parser FullPathDescription
fullPathDescription = FullPathDescription
  <$> (lparen *> listOfPathInputs)
  <*> optional polarityOperator
  <*> (star *> gt *> listOfPathOutputs)
  <?> "full_path_description"

listOfPathInputs :: Parser ListOfPathInputs
listOfPathInputs = specifyInputTerminalDescriptor `sepBy1` comma
  <?> "list_of_path_inputs"

listOfPathOutputs :: Parser ListOfPathOutputs
listOfPathOutputs = specifyOutputTerminalDescriptor `sepBy1` comma
  <?> "list_of_path_outputs"


-- | A.7.3 Specify block terminals
--

specifyInputTerminalDescriptor :: Parser SpecifyInputTerminalDescriptor
specifyInputTerminalDescriptor = SpecifyInputTerminalDescriptor
  <$> inputIdentifier
  <*> optional (between lbrack rbrack constantRangeExpression)
  <?> "specify_input_terminal_descriptor"

specifyOutputTerminalDescriptor :: Parser SpecifyOutputTerminalDescriptor
specifyOutputTerminalDescriptor = SpecifyOutputTerminalDescriptor
  <$> outputIdentifier
  <*> optional (between lbrack rbrack constantRangeExpression)
  <?> "specify_output_terminal_descriptor"

inputIdentifier :: Parser InputIdentifier
inputIdentifier
  =   InputPortIdentifier_InputIdentifier <$> inputPortIdentifier
  <|> InoutPortIdentifier_InputIdentifier <$> inoutPortIdentifier
  <|> PortIdentifier_InputIdentifier <$> interfaceIdentifier <*> (dot *> portIdentifier)
  <?> "input_identifier"

outputIdentifier :: Parser OutputIdentifier
outputIdentifier
  =   OutputPortIdentifier_OutputIdentifier <$> outputPortIdentifier
  <|> InoutPortIdentifier_OutputIdentifier <$> inoutPortIdentifier
  <|> PortIdentifier_OutputIdentifier <$> interfaceIdentifier <*> (dot *> portIdentifier)
  <?> "output_identifier"


-- | A.7.4 Specify path delays
--

pathDelayValue :: Parser PathDelayValue
pathDelayValue
  =   PathDelayValue <$> listOfPathDelayExpressions
  <|> PathDelayValue <$> between lparen rparen listOfPathDelayExpressions
  <?> "path_delay_value"

listOfPathDelayExpressions :: Parser ListOfPathDelayExpressions
listOfPathDelayExpressions
  =   TPathDelayExpression_ListOfPathDelayExpressions
      <$> tPathDelayExpression
  <|> RiseFall
      <$> trisePathDelayExpression
      <*> tfallPathDelayExpression
  <|> RiseFallZ
      <$> trisePathDelayExpression
      <*> tfallPathDelayExpression
      <*> tzPathDelayExpression
  <|> RiseFall01Z
      <$> t01PathDelayExpression
      <*> t10PathDelayExpression
      <*> t0zPathDelayExpression
      <*> tz1PathDelayExpression
      <*> t1zPathDelayExpression
      <*> tz0PathDelayExpression
  <|> RiseFall01XZ
      <$> t01PathDelayExpression
      <*> t10PathDelayExpression
      <*> t0zPathDelayExpression
      <*> tz1PathDelayExpression
      <*> t1zPathDelayExpression
      <*> tz0PathDelayExpression
      <*> t0xPathDelayExpression
      <*> tx1PathDelayExpression
      <*> t1xPathDelayExpression
      <*> tx0PathDelayExpression
      <*> txzPathDelayExpression
      <*> tzxPathDelayExpression
  <?> "list_of_path_delay_expressions"

tPathDelayExpression :: Parser TPathDelayExpression
tPathDelayExpression = pathDelayExpression <?> "t_path_delay_expression"

trisePathDelayExpression :: Parser TrisePathDelayExpression
trisePathDelayExpression = pathDelayExpression <?> "trise_path_delay_expression"

tfallPathDelayExpression :: Parser TfallPathDelayExpression
tfallPathDelayExpression = pathDelayExpression <?> "tfall_path_delay_expression"

tzPathDelayExpression :: Parser TzPathDelayExpression
tzPathDelayExpression = pathDelayExpression <?> "tz_path_delay_expression"

t01PathDelayExpression :: Parser T01PathDelayExpression
t01PathDelayExpression = pathDelayExpression <?> "t01_path_delay_expression"

t10PathDelayExpression :: Parser T10PathDelayExpression
t10PathDelayExpression = pathDelayExpression <?> "t10_path_delay_expression"

t0zPathDelayExpression :: Parser T0zPathDelayExpression
t0zPathDelayExpression = pathDelayExpression <?> "t0z_path_delay_expression"

tz1PathDelayExpression :: Parser Tz1PathDelayExpression
tz1PathDelayExpression = pathDelayExpression <?> "tz1_path_delay_expression"

t1zPathDelayExpression :: Parser T1zPathDelayExpression
t1zPathDelayExpression = pathDelayExpression <?> "t1z_path_delay_expression"

tz0PathDelayExpression :: Parser Tz0PathDelayExpression
tz0PathDelayExpression = pathDelayExpression <?> "tz0_path_delay_expression"

t0xPathDelayExpression :: Parser T0xPathDelayExpression
t0xPathDelayExpression = pathDelayExpression <?> "t0x_path_delay_expression"

tx1PathDelayExpression :: Parser Tx1PathDelayExpression
tx1PathDelayExpression = pathDelayExpression <?> "tx1_path_delay_expression"

t1xPathDelayExpression :: Parser T1xPathDelayExpression
t1xPathDelayExpression = pathDelayExpression <?> "t1x_path_delay_expression"

tx0PathDelayExpression :: Parser T1xPathDelayExpression
tx0PathDelayExpression = pathDelayExpression <?> "tx0_path_delay_expression"

txzPathDelayExpression :: Parser T1xPathDelayExpression
txzPathDelayExpression = pathDelayExpression <?> "txz_path_delay_expression"

tzxPathDelayExpression :: Parser T1xPathDelayExpression
tzxPathDelayExpression = pathDelayExpression <?> "tzx_path_delay_expression"

pathDelayExpression :: Parser PathDelayExpression
pathDelayExpression = constantMintypmaxExpression <?> "path_delay_expression"

edgeSensitivePathDeclaration :: Parser EdgeSensitivePathDeclaration
edgeSensitivePathDeclaration
  =   ParallelEdgeSensitivePathDescription_EdgeSensitivePathDeclaration
      <$> parallelEdgeSensitivePathDescription
      <*> (assign_op *> pathDelayValue)
  <|> FullEdgeSensitivePathDescription_EdgeSensitivePathDeclaration
      <$> fullEdgeSensitivePathDescription
      <*> (assign_op *> pathDelayValue)
  <?> "edge_sensitive_path_declaration"

parallelEdgeSensitivePathDescription :: Parser ParallelEdgeSensitivePathDescription
parallelEdgeSensitivePathDescription = ParallelEdgeSensitivePathDescription
  <$> (lparen *> optional edgeIdentifier)
  <*> specifyInputTerminalDescriptor
  <*> optional polarityOperator
  <*> (eq_arrow *> lparen *> specifyOutputTerminalDescriptor)
  <*> optional polarityOperator
  <*> (colon *> dataSourceExpression)
  <*  (rparen <* rparen)
  <?> "parallel_edge_sensitive_path_description"

fullEdgeSensitivePathDescription :: Parser FullEdgeSensitivePathDescription
fullEdgeSensitivePathDescription = FullEdgeSensitivePathDescription
  <$> (lparen *> optional edgeIdentifier)
  <*> listOfPathInputs
  <*> optional polarityOperator
  <*> (star *> gt *> lparen *> listOfPathOutputs)
  <*> optional polarityOperator
  <*> (colon *> dataSourceExpression)
  <*  (rparen <* rparen)
  <?> "full_edge_sensitive_path_description"

dataSourceExpression :: Parser DataSourceExpression
dataSourceExpression = expression <?> "data_source_expression"

edgeIdentifier :: Parser EdgeIdentifier
edgeIdentifier
  =   Posedge <$ posedge
  <|> Negedge <$ negedge
  <|> Edge <$ edge
  <?> "edge_identifier"

stateDependentPathDeclaration :: Parser StateDependentPathDeclaration
stateDependentPathDeclaration
  =   IfSimplePathDeclaration
      <$> (if_ *> between lparen rparen modulePathExpression)
      <*> simplePathDeclaration
  <|> IfEdgeSensitivePathDeclaration
      <$> (if_ *> between lparen rparen modulePathExpression)
      <*> edgeSensitivePathDeclaration
  <|> IfNoneSimplePathDeclaration
      <$> (ifnone *> simplePathDeclaration)
  <?> "state_dependent_path_declaration"

polarityOperator :: Parser PolarityOperator
polarityOperator = PlusPol <$ plus <|> MinusPol <$ minus
  <?> "polarity_operator"


-- | A.7.5 System timing checks
--
--   A.7.5.1 System timing check commands
--

systemTimingCheck :: Parser SystemTimingCheck
systemTimingCheck
  =   SetupTimingCheck_SystemTimingCheck <$> setupTimingCheck
  <|> HoldTimingCheck_SystemTimingCheck <$> holdTimingCheck
  <|> SetupholdTimingCheck_SystemTimingCheck <$> setupholdTimingCheck
  <|> RecoveryTimingCheck_SystemTimingCheck <$> recoveryTimingCheck
  <|> RemovalTimingCheck_SystemTimingCheck <$> removalTimingCheck
  <|> RecremTimingCheck_SystemTimingCheck <$> recremTimingCheck
  <|> SkewTimingCheck_SystemTimingCheck <$> skewTimingCheck
  <|> TimeskewTimingCheck_SystemTimingCheck <$> timeskewTimingCheck
  <|> FullskewTimingCheck_SystemTimingCheck <$> fullskewTimingCheck
  <|> PeriodTimingCheck_SystemTimingCheck <$> periodTimingCheck
  <|> WidthTimingCheck_SystemTimingCheck <$> widthTimingCheck
  <|> NochangeTimingCheck_SystemTimingCheck <$> nochangeTimingCheck
  <?> "system_timing_check"

setupTimingCheck :: Parser SetupTimingCheck
setupTimingCheck = SetupTimingCheck
  <$> (tf_setup *> lparen *> dataEvent)
  <*> (comma *> referenceEvent)
  <*> (comma *> timingCheckLimit)
  <*> optional (comma *> optional notifier)
  <*  (rparen <* semi)
  <?> "setup_timing_check"

holdTimingCheck :: Parser HoldTimingCheck
holdTimingCheck = HoldTimingCheck
  <$> (tf_hold *> lparen *> referenceEvent)
  <*> (comma *> dataEvent)
  <*> (comma *> timingCheckLimit)
  <*> optional (comma *> optional notifier)
  <*  (rparen <* semi)
  <?> "hold_timing_check"

setupholdTimingCheck :: Parser SetupholdTimingCheck
setupholdTimingCheck = SetupholdTimingCheck
  <$> (tf_setuphold *> lparen *> referenceEvent)
  <*> (comma *> dataEvent)
  <*> (comma *> timingCheckLimit)
  <*> (comma *> timingCheckLimit)
  <*> optional (comma >> (,) <$> optional notifier
      <*> optional (comma >> (,) <$> optional timestampCondition
        <*> optional (comma >> (,) <$> optional timecheckCondition
          <*> optional (comma >> (,) <$> optional delayedReference
            <*> optional (comma >> optional delayedData)))))
  <*  (lparen <* semi)
  <?> "setuphold_timing_check"

recoveryTimingCheck :: Parser RecoveryTimingCheck
recoveryTimingCheck = RecoveryTimingCheck
  <$> (tf_recovery *> lparen *> referenceEvent)
  <*> (comma *> dataEvent)
  <*> (comma *> timingCheckLimit)
  <*> optional (comma *> optional notifier)
  <*  (rparen <* semi)
  <?> "recovery_timing_check"

removalTimingCheck :: Parser RemovalTimingCheck
removalTimingCheck = RemovalTimingCheck
  <$> (tf_removal *> lparen *> referenceEvent)
  <*> (comma *> dataEvent)
  <*> (comma *> timingCheckLimit)
  <*> optional (comma *> optional notifier)
  <*  (rparen <* semi)
  <?> "removal_timing_check"

recremTimingCheck :: Parser RecremTimingCheck
recremTimingCheck = RecremTimingCheck
  <$> (tf_recrem *> lparen *> referenceEvent)
  <*> (comma *> dataEvent)
  <*> (comma *> timingCheckLimit)
  <*> (comma *> timingCheckLimit)
  <*> optional (comma >> (,) <$> optional notifier
      <*> optional (comma >> (,) <$> optional timestampCondition
        <*> optional (comma >> (,) <$> optional timecheckCondition
          <*> optional (comma >> (,) <$> optional delayedReference
            <*> optional (comma >> optional delayedData)))))
  <*  (lparen <* semi)
  <?> "recrem_timing_check"

skewTimingCheck :: Parser SkewTimingCheck
skewTimingCheck = SkewTimingCheck
  <$> (tf_skew *> lparen *> referenceEvent)
  <*> (comma *> dataEvent)
  <*> (comma *> timingCheckLimit)
  <*> optional (comma *> optional notifier)
  <*  (rparen <* semi)
  <?> "skew_timing_check"

timeskewTimingCheck :: Parser TimeskewTimingCheck
timeskewTimingCheck = TimeskewTimingCheck
  <$> (tf_timeskew *> lparen *> referenceEvent)
  <*> (comma *> dataEvent)
  <*> (comma *> timingCheckLimit)
  <*> optional (comma >> (,) <$> optional notifier
      <*> optional (comma >> (,) <$> optional eventBasedFlag
        <*> optional (comma >> optional remainActiveFlag)))
  <?> "timeskew_timing_check"

fullskewTimingCheck :: Parser FullskewTimingCheck
fullskewTimingCheck = FullskewTimingCheck
  <$> (tf_fullskew *> lparen *> referenceEvent)
  <*> (comma *> dataEvent)
  <*> (comma *> timingCheckLimit)
  <*> (comma *> timingCheckLimit)
  <*> optional (comma >> (,) <$> optional notifier
      <*> optional (comma >> (,) <$> optional eventBasedFlag
        <*> optional (comma >> optional remainActiveFlag)))
  <?> "fullskew_timing_check"

periodTimingCheck :: Parser PeriodTimingCheck
periodTimingCheck = PeriodTimingCheck
  <$> (tf_period *> lparen *> controlledReferenceEvent)
  <*> (comma *> timingCheckLimit)
  <*> optional (comma *> optional notifier)
  <*  (rparen <* semi)
  <?> "period_timing_check"

widthTimingCheck :: Parser WidthTimingCheck
widthTimingCheck = WidthTimingCheck
  <$> (tf_period *> lparen *> controlledReferenceEvent)
  <*> (comma *> timingCheckLimit)
  <*> (comma *> threshold)
  <*> optional (comma *> optional notifier)
  <*  (rparen <* semi)
  <?> "width_timing_check"

nochangeTimingCheck :: Parser NochangeTimingCheck
nochangeTimingCheck = NochangeTimingCheck
  <$> (tf_nochange *> lparen *> referenceEvent)
  <*> (comma *> dataEvent)
  <*> (comma *> startEdgeOffset)
  <*> (comma *> endEdgeOffset)
  <*> optional (comma *> optional notifier)
  <*  (rparen <* semi)
  <?> "nochange_timing_check"

-- | A.7.5.2 System timing check command arguments
--

timecheckCondition :: Parser TimecheckCondition
timecheckCondition = mintypmaxExpression <?> "timecheck_condition"

controlledReferenceEvent :: Parser ControlledReferenceEvent
controlledReferenceEvent = controlledTimingCheckEvent <?> "controlled_reference_event"

dataEvent :: Parser DataEvent
dataEvent = timingCheckEvent <?> "data_event"

delayedData :: Parser DelayedData
delayedData = DelayedData
  <$> terminalIdentifier
  <*> optional (between lbrack rbrack constantMintypmaxExpression)
  <?> "delayed_data"

delayedReference :: Parser DelayedReference
delayedReference = DelayedReference
  <$> terminalIdentifier
  <*> optional (between lbrack rbrack constantMintypmaxExpression)
  <?> "delayed_reference"

endEdgeOffset :: Parser EndEdgeOffset
endEdgeOffset = mintypmaxExpression <?> "end_edge_offset"

eventBasedFlag :: Parser EventBasedFlag
eventBasedFlag = constantExpression <?> "event_based_flag"

notifier :: Parser Notifier
notifier = variableIdentifier <?> "notifier"

referenceEvent :: Parser ReferenceEvent
referenceEvent = timingCheckEvent <?> "reference_event"

remainActiveFlag :: Parser RemainActiveFlag
remainActiveFlag = constantMintypmaxExpression <?> "remain_active_flag"

timestampCondition :: Parser TimestampCondition
timestampCondition = mintypmaxExpression <?> "timestamp_condition"

startEdgeOffset :: Parser StartEdgeOffset
startEdgeOffset = mintypmaxExpression <?> "start_edge_offset"

threshold :: Parser Threshold
threshold = constantExpression <?> "threshold"

timingCheckLimit :: Parser TimingCheckLimit
timingCheckLimit = expression <?> "timing_check_limit"

-- | A.7.5.3 System timing check event defintions
--

timingCheckEvent :: Parser TimingCheckEvent
timingCheckEvent = TimingCheckEvent
  <$> optional timingCheckEventControl
  <*> specifyTerminalDescriptor
  <*> optional (triple_amp *> timingCheckCondition)
  <?> "timing_check_event"

controlledTimingCheckEvent :: Parser ControlledTimingCheckEvent
controlledTimingCheckEvent = ControlledTimingCheckEvent
  <$> timingCheckEventControl
  <*> specifyTerminalDescriptor
  <*> optional (triple_amp *> timingCheckCondition)
  <?> "controlled_timing_check_event"

timingCheckEventControl :: Parser TimingCheckEventControl
timingCheckEventControl
  =   EdgeIdentifier_TimingCheckEventControl <$> edgeIdentifier
  <|> EdgeControlSpecifier_TimingCheckEventControl <$> edgeControlSpecifier
  <?> "timing_check_event_control"

specifyTerminalDescriptor :: Parser SpecifyTerminalDescriptor
specifyTerminalDescriptor
  =   Left  <$> specifyInputTerminalDescriptor
  <|> Right <$> specifyOutputTerminalDescriptor
  <?> "specify_terminal_descriptor"

edgeControlSpecifier :: Parser EdgeControlSpecifier
edgeControlSpecifier = EdgeControlSpecifier
  <$> (edge *> between lbrack lbrack (edgeDescriptor `sepBy1` comma))
  <?> "edge_control_specifier"

edgeDescriptor :: Parser EdgeDescriptor
edgeDescriptor = number <?> "edge_descriptor"

zeroOrOne :: Parser ZeroOrOne
zeroOrOne = number <?> "zero_or_one"

zOrX :: Parser ZOrX
zOrX = number <?> "z_or_x"

timingCheckCondition :: Parser TimingCheckCondition
timingCheckCondition
  =   scalarTimingCheckCondition
  <|> between lparen rparen scalarTimingCheckCondition
  <?> "timing_check_condition"

scalarTimingCheckCondition :: Parser ScalarTimingCheckCondition
scalarTimingCheckCondition
  =   ScalarTimingCheckConditionNot <$> (tilde *> expression)
  <|> ScalarTimingCheckConditionEquals <$> expression <*> (eq *> scalarConstant)
  <|> ScalarTimingCheckConditionEquivalent <$> expression <*> (equivalent *> scalarConstant)
  <|> ScalarTimingCheckConditionNotEquals <$> expression <*> (noteq *> scalarConstant)
  <|> ScalarTimingCheckConditionNotEquivalent <$> expression <*> (not_equivalent *> scalarConstant)
  <|> ScalarTimingCheckCondition <$> expression
  <?> "scalar_timing_check_condition"

scalarConstant :: Parser ScalarConstant
scalarConstant = number <?> "scalar_constant"


-- | A.8 Expressions
--
--   A.8.1 Concatenations
--

concatenation :: Parser Concatenation
concatenation = between lbrace rbrace (expression `sepBy1` comma)
  <?> "concatenation"

constantConcatenation :: Parser ConstantConcatenation
constantConcatenation = between lbrace rbrace (constantExpression `sepBy1` comma)
  <?> "constant_concatenation"

constantMultipleConcatenation :: Parser ConstantMultipleConcatenation
constantMultipleConcatenation = ConstantMultipleConcatenation
  <$> (lbrace *> constantExpression)
  <*> (constantConcatenation <* rbrace)
  <?> "constant_multiple_concatenation"

modulePathConcatenation :: Parser ModulePathConcatenation
modulePathConcatenation = between lbrace rbrace (modulePathExpression `sepBy1` comma)
  <?> "module_path_concatenation"

modulePathMultipleConcatenation :: Parser ModulePathMultipleConcatenation
modulePathMultipleConcatenation = ModulePathMultipleConcatenation
  <$> (lbrace *> constantExpression)
  <*> (modulePathConcatenation <* rbrace)
  <?> "module_path_multiple_concatenation"

multipleConcatenation :: Parser MultipleConcatenation
multipleConcatenation = MultipleConcatenation
  <$> (lbrace *> expression)
  <*> (concatenation <* rbrace)
  <?> "multiple_concatenation"

streamingConcatenation :: Parser StreamingConcatenation
streamingConcatenation = StreamingConcatenation
  <$> (lbrace *> streamOperator)
  <*> optional sliceSize
  <*> streamConcatenation
  <*  rbrace
  <?> "streaming_concatenation"

streamOperator :: Parser StreamOperator
streamOperator = Downstream <$ gtgt <|> Upstream <$ ltlt
  <?> "stream_operator"

sliceSize :: Parser SliceSize
sliceSize
  =   SimpleType_SliceSize <$> simpleType
  <|> ConstantExpression_SliceSize <$> constantExpression
  <?> "slice_size"

streamConcatenation :: Parser StreamConcatenation
streamConcatenation = between lbrace rbrace (streamExpression `sepBy1` comma)
  <?> "stream_concatenation"

streamExpression :: Parser StreamExpression
streamExpression = StreamExpression
  <$> expression
  <*> optional (with *> between lbrack rbrack arrayRangeExpression)
  <?> "stream_expression"

arrayRangeExpression :: Parser ArrayRangeExpression
arrayRangeExpression
  =   ArrayRangeZ <$> expression <*> (colon *> expression)
  <|> ArrayRangeP <$> expression <*> (plus *> colon *> expression)
  <|> ArrayRangeM <$> expression <*> (minus *> colon *> expression)
  <|> Expression_ArrayRangeExpression <$> expression
  <?> "array_range_expression"

emptyQueue :: Parser EmptyQueue
emptyQueue = EmptyQueue <$ lbrack <* rbrack
  <?> "empty_queue"


-- | A.8.2 Subroutine calls
--

constantFunctionCall :: Parser ConstantFunctionCall
constantFunctionCall = functionSubroutineCall <?> "constant_function_call"

tfCall :: Parser TfCall
tfCall = TfCall
  <$> psOrHierarchicalTfIdentifier
  <*> many attributeInstance
  <*> optional (between lparen rparen listOfArguments)
  <?> "tf_call"

systemTfCall :: Parser SystemTfCall
systemTfCall
  =   ListOfArguments_SystemTfCall
      <$> systemTfIdentifier
      <*> optional (between lparen rparen listOfArguments)
  <|> DataType_SystemTfCall
      <$> systemTfIdentifier
      <*> (lparen *> dataType)
      <*> optional (comma *> expression)
      <*  rparen
  <?> "system_tf_call"

subroutineCall :: Parser SubroutineCall
subroutineCall
  =   TfCall_SubroutineCall <$> tfCall
  <|> SystemTfCall_SubroutineCall <$> systemTfCall
  <|> MethodCall_SubroutineCall <$> methodCall
  <|> RandomizeCall_SubroutineCall <$> optional (std *> namequal) <*> randomizeCall
  <?> "subroutine_call"

functionSubroutineCall :: Parser FunctionSubroutineCall
functionSubroutineCall = subroutineCall <?> "function_subroutine_call"

listOfArguments :: Parser ListOfArguments
listOfArguments
  =   ListOfArguments
      <$> (Just <$> sepBy1 (optional expression) comma)
      <*> sepBy ((,) <$> (dot *> identifier) <*> between lparen rparen (optional expression)) comma
  <|> ListOfArguments
      <$> pure Nothing
      <*> sepBy1 ((,) <$> (dot *> identifier) <*> between lparen rparen (optional expression)) comma
  <?> "list_of_arguments"

methodCall :: Parser MethodCall
methodCall = MethodCall
  <$> methodCallRoot
  <*> (dot *> methodCallBody)
  <?> "method_call"

methodCallBody :: Parser MethodCallBody
methodCallBody
  =   MethodCallBody
      <$> methodIdentifier
      <*> many attributeInstance
      <*> optional (between lparen rparen listOfArguments)
  <|> BuiltInMethodCall_MethodCallBody
      <$> builtInMethodCall
  <?> "method_call_body"

builtInMethodCall :: Parser BuiltInMethodCall
builtInMethodCall
  =   ArrayManipulationCall_BuiltInMethodCall <$> arrayManipulationCall
  <|> RandomizeCall_BuiltInMethodCall <$> randomizeCall
  <?> "built_in_method_call"

arrayManipulationCall :: Parser ArrayManipulationCall
arrayManipulationCall = ArrayManipulationCall
  <$> arrayMethodName
  <*> many attributeInstance
  <*> optional (between lparen rparen listOfArguments)
  <*> optional (with *> between lparen rparen expression)
  <?> "array_manipulation_call"

randomizeCall :: Parser RandomizeCall
randomizeCall = RandomizeCall
  <$> (randomize *> many attributeInstance)
  <*> optional
      (between lparen rparen (optional (Left <$> variableIdentifierList <|> Right <$> null_)))
  <*> optional
      (with >> (,) <$> optional (between lparen rparen (optional identifierList)) <*> constraintBlock)
  <?> "randomize_call"

methodCallRoot :: Parser MethodCallRoot
methodCallRoot = Left <$> primary <|> Right <$> implicitClassHandle
  <?> "method_call_root"

arrayMethodName :: Parser ArrayMethodName
arrayMethodName
  =   MethodIdentifier_ArrayMethodName <$> methodIdentifier
  <|> UniqueAM <$ unique
  <|> AndAM    <$ and_
  <|> OrAM     <$ or_
  <|> XorAM    <$ xor
  <?> "array_method_name"


-- | A.8.3 Expressions
--

incOrDecExpression :: Parser IncOrDecExpression
incOrDecExpression
  =   PrefixIncOrDecExpression
      <$> incOrDecOperator
      <*> many attributeInstance
      <*> variableLvalue
  <|> PostfixIncOrDecExpression
      <$> variableLvalue
      <*> many attributeInstance
      <*> incOrDecOperator
  <?> "inc_or_dec_expression"

conditionalExpression :: Parser ConditionalExpression
conditionalExpression = ConditionalExpression
  <$> condPredicate
  <*> (question *> many attributeInstance)
  <*> expression
  <*> (colon *> expression)
  <?> "conditional_expression"

constantExpression :: Parser ConstantExpression
constantExpression
  =   ConstantPrimary_ConstantExpression
      <$> constantPrimary
  <|> UnaryConstantExpression
      <$> unaryOperator
      <*> many attributeInstance
      <*> constantPrimary
  <|> BinaryConstantExpression
      <$> constantExpression
      <*> binaryOperator
      <*> many attributeInstance
      <*> constantExpression
  <|> TertiaryConstantExpression
      <$> constantExpression
      <*> (question *> many attributeInstance)
      <*> constantExpression
      <*> (colon *> constantExpression)
  <?> "constant_expression"

constantMintypmaxExpression :: Parser ConstantMintypmaxExpression
constantMintypmaxExpression
  =   Right <$> ((,,)
      <$> constantExpression
      <*> (colon *> constantExpression)
      <*> (colon *> constantExpression))
  <|> Left <$> constantExpression
  <?> "constant_mintypmax_expression"

constantParamExpression :: Parser ConstantParamExpression
constantParamExpression
  =   ConstantMintypmaxExpression_ConstantParamExpression <$> constantMintypmaxExpression
  <|> DataType_ConstantParamExpression <$> dataType
  <|> DollarConstantParamExpression <$ dollar
  <?> "constant_param_expression"

paramExpression :: Parser ParamExpression
paramExpression
  =   MintypmaxExpression_ParamExpression <$> mintypmaxExpression
  <|> DataType_ParamExpression <$> dataType
  <|> DollarParamExpression <$ dollar
  <?> "param_expression"

constantRangeExpression :: Parser ConstantRangeExpression
constantRangeExpression = Left <$> constantExpression <|> Right <$> constantPartSelectRange
  <?> "constant_range_expression"

constantPartSelectRange :: Parser ConstantPartSelectRange
constantPartSelectRange = Left <$> constantRange <|> Right <$> constantIndexedRange
  <?> "constant_part_select_range"

constantRange :: Parser ConstantRange
constantRange = (,)
  <$> constantExpression
  <*> (colon *> constantExpression)
  <?> "constant_range"

constantIndexedRange :: Parser ConstantIndexedRange
constantIndexedRange
  =   PlusConstantIndexedRange
      <$> constantExpression
      <*> (plus *> colon *> constantExpression)
  <|> MinusConstantIndexedRange
      <$> constantExpression
      <*> (minus *> colon *> constantExpression)
  <?> "constant_indexed_range"

expression :: Parser Expression
expression
  =   Primary_Expression
      <$> primary
  <|> UnaryExpression
      <$> unaryOperator
      <*> many attributeInstance
      <*> primary
  <|> IncOrDecExpression_Expression
      <$> incOrDecExpression
  <|> OperatorAssignment_Expression
      <$> between lparen rparen operatorAssignment
  <|> BinaryExpression
      <$> expression
      <*> binaryOperator
      <*> many attributeInstance
      <*> expression
  <|> ConditionalExpression_Expression
      <$> conditionalExpression
  <|> InsideExpression_Expression
      <$> insideExpression
  <|> TaggedUnionExpression_Expression
      <$> taggedUnionExpression
  <?> "expression"

taggedUnionExpression :: Parser TaggedUnionExpression
taggedUnionExpression = TaggedUnionExpression
  <$> (tagged *> memberIdentifier)
  <*> optional expression
  <?> "tagged_union_expression"

insideExpression :: Parser InsideExpression
insideExpression = InsideExpression
  <$> expression
  <*> (inside *> between lbrack rbrack openRangeList)
  <?> "inside_expression"

valueRange :: Parser ValueRange
valueRange
  =   Left  <$> expression
  <|> Right <$> between lbrack rbrack ((,) <$> expression <*> (colon *> expression))
  <?> "value_range"

mintypmaxExpression :: Parser MintypmaxExpression
mintypmaxExpression
  =   Right <$> ((,,)
      <$> expression
      <*> (colon *> expression)
      <*> (colon *> expression))
  <|> Left <$> expression
  <?> "mintypmax_expression"

modulePathConditionalExpression :: Parser ModulePathConditionalExpression
modulePathConditionalExpression = ModulePathConditionalExpression
  <$> modulePathExpression
  <*> (question *> many attributeInstance)
  <*> modulePathExpression
  <*> (colon *> modulePathExpression)
  <?> "module_path_conditional_expression"

modulePathExpression :: Parser ModulePathExpression
modulePathExpression
  =   ModulePathPrimary_ModulePathExpression
      <$> modulePathPrimary
  <|> UnaryModulePathExpression
      <$> unaryModulePathOperator
      <*> many attributeInstance
      <*> modulePathPrimary
  <|> BinaryModulePathExpression
      <$> modulePathExpression
      <*> binaryModulePathOperator
      <*> many attributeInstance
      <*> modulePathExpression
  <|> ModulePathConditionalExpression_ModulePathExpression
      <$> modulePathConditionalExpression
  <?> "module_path_expression"

modulePathMintypmaxExpression :: Parser ModulePathMintypmaxExpression
modulePathMintypmaxExpression
  =   Right <$> ((,,)
      <$> modulePathExpression
      <*> (colon *> modulePathExpression)
      <*> (colon *> modulePathExpression))
  <|> Left <$> modulePathExpression
  <?> "module_path_mintypmax_expression"

partSelectRange :: Parser PartSelectRange
partSelectRange = Left <$> constantRange <|> Right <$> indexedRange
  <?> "part_select_range"

indexedRange :: Parser IndexedRange
indexedRange
  =   PlusIndexedRange
      <$> expression
      <*> (plus *> colon *> constantExpression)
  <|> MinusIndexedRange
      <$> expression
      <*> (minus *> colon *> constantExpression)
  <?> "indexed_range"

genvarExpression :: Parser GenvarExpression
genvarExpression = constantExpression <?> "genvar_expression"


-- | A.8.4 Primaries
--

constantPrimary :: Parser ConstantPrimary
constantPrimary
  =   PrimaryLiteral_ConstantPrimary
      <$> primaryLiteral
  <|> PsParameterIdentifier_ConstantPrimary
      <$> psParameterIdentifier
      <*> constantSelect
  <|> SpecparamIdentifier_ConstantPrimary
      <$> specparamIdentifier
      <*> optional constantRangeExpression
  <|> GenvarIdentifier_ConstantPrimary
      <$> genvarIdentifier
  <|> FormalPortIdentifier_ConstantPrimary
      <$> formalPortIdentifier
      <*> constantSelect
  <|> EnumIdentifier_ConstantPrimary
      <$> optional (Left <$> packageScope <|> Right <$> classScope)
      <*> enumIdentifier
  <|> ConstantConcatenation_ConstantPrimary
      <$> constantConcatenation
      <*> optional (between lbrack rbrack constantRangeExpression)
  <|> ConstantMultipleConcatenation_ConstantPrimary
      <$> constantMultipleConcatenation
      <*> optional (between lbrack rbrack constantRangeExpression)
  <|> ConstantFunctionCall_ConstantPrimary
      <$> constantFunctionCall
  <|> ConstantLetExpression_ConstantPrimary
      <$> constantLetExpression
  <|> ConstantMintypmaxExpression_ConstantPrimary
      <$> between lparen rparen constantMintypmaxExpression
  <|> ConstantCast_ConstantPrimary
      <$> constantCast
  <|> ConstantAssignmentPatternExpression_ConstantPrimary
      <$> constantAssignmentPatternExpression
  <|> TypeReference_ConstantPrimary
      <$> typeReference
  <?> "constant_primary"

modulePathPrimary :: Parser ModulePathPrimary
modulePathPrimary
  =   Number_ModulePathPrimary <$> number
  <|> Identifier_ModulePathPrimary <$> identifier
  <|> ModulePathConcatenation_ModulePathPrimary <$> modulePathConcatenation
  <|> ModulePathMultipleConcatenation_ModulePathPrimary <$> modulePathMultipleConcatenation
  <|> FunctionSubroutineCall_ModulePathPrimary <$> functionSubroutineCall
  <|> ModulePathMintypmaxExpression_ModulePathPrimary
      <$> between lparen rparen modulePathMintypmaxExpression
  <?> "module_path_primary"

primary :: Parser Primary
primary
  =   PrimaryLiteral_Primary <$> primaryLiteral
  <|> HierarchicalIdentifier_Primary
      <$> optional (Left <$> classQualifier <|> Right <$> packageScope)
      <*> hierarchicalIdentifier
      <*> select
  <|> EmptyPrimary <$ emptyQueue
  <|> Concatenation_Primary
      <$> concatenation
      <*> optional (between lbrack rbrack rangeExpression)
  <|> MultipleConcatenation_Primary
      <$> multipleConcatenation
      <*> optional (between lbrack rbrack rangeExpression)
  <|> FunctionSubroutineCall_Primary <$> functionSubroutineCall
  <|> LetExpression_Primary <$> letExpression
  <|> MintypmaxExpression_Primary
      <$> between lparen rparen mintypmaxExpression
  <|> Cast_Primary <$> cast
  <|> AssignmentPatternExpression_Primary <$> assignmentPatternExpression
  <|> StreamingConcatenation_Primary <$> streamingConcatenation
  <|> SequenceMethodCall_Primary <$> sequenceMethodCall
  <|> ThisPrimary   <$ this
  <|> DollarPrimary <$ dollar
  <|> NullPrimary   <$ null_
  <?> "primary"

classQualifier :: Parser ClassQualifier
classQualifier = ClassQualifier
  <$> optional (local *> namequal)
  <*> optional (Left <$> implicitClassHandle <* dot <|> Right <$> classScope)
  <?> "class_qualifier"

rangeExpression :: Parser RangeExpression
rangeExpression = Left <$> expression <|> Right <$> partSelectRange
  <?> "range_expression"

primaryLiteral :: Parser PrimaryLiteral
primaryLiteral
  =   Number_PrimaryLiteral <$> number
  <|> TimeLiteral_PrimaryLiteral <$> timeLiteral
  <|> UnbasedUnsizedLiteral_PrimaryLiteral <$> unbasedUnsizedLiteral
  <|> StringLiteral_PrimaryLiteral <$> stringLiteral
  <?> "primary_literal"

timeLiteral :: Parser TimeLiteral
timeLiteral
  =   UnsignedTimeLiteral <$> unsignedNumber <*> timeUnit
  <|> FixedPointTimeLiteral <$> fixedPointNumber <*> timeUnit
  <?> "time_literal"

timeUnit :: Parser TimeUnit
timeUnit = identifier <?> "time_unit"

implicitClassHandle :: Parser ImplicitClassHandle
implicitClassHandle
  =   ThisSuper <$ this <* dot <* super
  <|> Super <$ super
  <|> This <$ this
  <?> "implicit_class_handle"

bitSelect :: Parser BitSelect
bitSelect = many (between lbrack rbrack expression)
  <?> "bit_select"

select :: Parser Select
select = Select
  <$> optional
      ((,) <$> many ((,) <$> (dot *> memberIdentifier) <*> bitSelect) <*> (dot *> memberIdentifier))
  <*> bitSelect
  <*> optional (between lbrack rbrack partSelectRange)
  <?> "select"

nonrangeSelect :: Parser NonrangeSelect
nonrangeSelect = NonrangeSelect
  <$> optional
      ((,)
        <$> many ((,) <$> (dot *> memberIdentifier) <*> bitSelect)
        <*> (dot *> memberIdentifier))
  <*> bitSelect
  <?> "nonrange_select"

constantBitSelect :: Parser ConstantBitSelect
constantBitSelect = many (between lbrack rbrack constantExpression)
  <?> "constant_bit_select"

constantSelect :: Parser ConstantSelect
constantSelect = ConstantSelect
  <$> optional
      ((,)
        <$> many ((,) <$> (dot *> memberIdentifier) <*> constantBitSelect)
        <*> (dot *> memberIdentifier))
  <*> constantBitSelect
  <*> optional (between lbrack rbrack constantPartSelectRange)
  <?> "constant_select"

constantCast :: Parser ConstantCast
constantCast = ConstantCast
  <$> castingType
  <*> (apostrophe *> between lparen rparen constantExpression)
  <?> "constant_cast"

constantLetExpression :: Parser ConstantLetExpression
constantLetExpression = letExpression <?> "constan_let_expression"

cast :: Parser Cast
cast = Cast
  <$> castingType
  <*> (apostrophe *> between lparen rparen expression)
  <?> "cast"

-- | A.8.5 Expression left-side values
--

netLvalue :: Parser NetLvalue
netLvalue
  =   PsOrHierarchicalNetIdentifier_NetLvalue
      <$> psOrHierarchicalNetIdentifier
      <*> constantSelect
  <|> NetLvalues_NetLvalue
      <$> between lbrace rbrace (netLvalue `sepBy1` comma)
  <|> AssignmentPatternNetLvalue_NetLvalue
      <$> optional assignmentPatternExpressionType
      <*> assignmentPatternNetLvalue
  <?> "net_lvalue"

variableLvalue :: Parser VariableLvalue
variableLvalue
  =   HierarchicalVariableIdentifier_VariableLvalue
      <$> hierarchicalVariableIdentifier
      <*> select
  <|> VariableLvalues_VariableLvalue
      <$> between lbrace rbrace (variableLvalue `sepBy1` comma)
  <|> AssignmentPatternVariableLvalue_VariableLvalue
      <$> optional assignmentPatternExpressionType
      <*> assignmentPatternVariableLvalue
  <|> StreamingConcatenation_VariableLvalue
      <$> streamingConcatenation
  <?> "variable_lvalue"

nonrangeVariableLvalue :: Parser NonrangeVariableLvalue
nonrangeVariableLvalue = NonrangeVariableLvalue
  <$> optional (Left <$> implicitClassHandle <* dot <|> Right <$> packageScope)
  <*> hierarchicalVariableIdentifier
  <*> nonrangeSelect
  <?> "nonrange_variable_lvalue"


-- | A.8.6 Operators
--

unaryOperator :: Parser UnaryOperator
unaryOperator
  =   NotUn <$ not_op
  <|> TildeAmpUn  <$ tilde <* amp 
  <|> TildePipeUn <$ tilde <* pipe
  <|> CaretTildeUn <$ caret <* tilde
  <|> TildeCaretUn <$ tilde <* caret
  <|> AmpUn   <$ amp
  <|> PipeUn  <$ pipe
  <|> TildeUn <$ tilde
  <|> CaretUn <$ caret
  <?> "unary_operator"


binaryOperator :: Parser BinaryOperator
binaryOperator
  =   PlusBin  <$ plus
  <|> MinusBin <$ minus
  <|> StarBin  <$ star
  <|> SlashBin <$ slash
  <|> PercentBin <$ percent
  <|> EqualsBin    <$ eq
  <|> NotEqualsBin <$ noteq
  <|> EquivalentBin    <$ equivalent
  <|> NotEquivalentBin <$ not_equivalent
  <|> AndBin <$ and_op
  <|> OrBin  <$ or_op
  <|> AmpBin  <$ amp
  <|> PipeBin <$ pipe
  <|> CaretTildeBin <$ caret <* tilde
  <|> TildeCaretBin <$ tilde <* caret
  <|> CaretBin <$ caret
  <?> "binary_operator"

incOrDecOperator :: Parser IncOrDecOperator
incOrDecOperator = Increment <$ increment <|> Decrement <$ decrement
  <?> "inc_or_dec_operator"

unaryModulePathOperator :: Parser UnaryModulePathOperator
unaryModulePathOperator
  =   NotUn <$ not_op
  <|> TildeAmpUn  <$ tilde <* amp 
  <|> TildePipeUn <$ tilde <* pipe
  <|> CaretTildeUn <$ caret <* tilde
  <|> TildeCaretUn <$ tilde <* caret
  <|> AmpUn   <$ amp
  <|> PipeUn  <$ pipe
  <|> TildeUn <$ tilde
  <|> CaretUn <$ caret
  <?> "unary_module_path_operator"

binaryModulePathOperator :: Parser BinaryModulePathOperator
binaryModulePathOperator
  =   EqualsBin    <$ eq
  <|> NotEqualsBin <$ noteq
  <|> AndBin <$ and_op
  <|> OrBin  <$ or_op
  <|> AmpBin  <$ amp
  <|> PipeBin <$ pipe
  <|> CaretTildeBin <$ caret <* tilde
  <|> TildeCaretBin <$ tilde <* caret
  <|> CaretBin <$ caret
  <?> "binary_module_path_operator"


-- | A.8.7 Numbers
--
number :: Parser Number
number
  =   IntegralNumber_Number <$> integralNumber
  <|> RealNumber_Number <$> realNumber
  <?> "number"

integralNumber :: Parser IntegralNumber
integralNumber
  =   DecimalNumber_IntegralNumber <$> decimalNumber
  <|> OctalNumber_IntegralNumber <$> octalNumber
  <|> BinaryNumber_IntegralNumber <$> binaryNumber
  <|> HexNumber_IntegralNumber <$> hexNumber
  <?> "integral_number"

decimalNumber :: Parser DecimalNumber
decimalNumber
  =   UnsignedNumber_DecimalNumber
      <$> pure Nothing
      <*> unsignedNumber
  <|> UnsignedNumber_DecimalNumber
      <$> optional size
      <*> (decimalBase *> unsignedNumber)
  <|> X_DecimalNumber
      <$> optional size
      <*> (decimalBase *> xdigit)
  <|> Z_DecimalNumber
      <$> optional size
      <*> (decimalBase *> zdigit)
  <?> "decimal_number"

binaryNumber :: Parser BinaryNumber
binaryNumber = BinaryNumber
  <$> optional size
  <*> (binaryBase *> binaryValue)
  <?> "binary_number"

octalNumber :: Parser OctalNumber
octalNumber = OctalNumber
  <$> optional size
  <*> (octalBase *> octalValue)
  <?> "octal_number"

hexNumber :: Parser HexNumber
hexNumber = HexNumber
  <$> optional size
  <*> (hexBase *> hexValue)
  <?> "hex_number"

realNumber :: Parser RealNumber
realNumber
  =   FixedPointNumber_RealNumber
      <$> fixedPointNumber
  <|> UnsignedNumber_RealNumber
      <$> unsignedNumber
      <*> optional (dot *> unsignedNumber)
      <*> (exp_ *> optional sign)
      <*> unsignedNumber
  <?> "real_number"

fixedPointNumber :: Parser FixedPointNumber
fixedPointNumber = (,)
  <$> unsignedNumber
  <*> (dot *> unsignedNumber)
  <?> "fixed_point_number"

sign :: Parser Sign
sign = Plus <$ plus <|> Minus <$ minus <?> "sign"

unsignedNumber :: Parser UnsignedNumber
unsignedNumber = unsigned_number <?> "unsigned_number"

binaryValue :: Parser BinaryValue
binaryValue = binary_value <?> "binary_value"

octalValue :: Parser OctalValue
octalValue = octal_value <?> "octal_value"

hexValue :: Parser HexValue
hexValue = hex_value <?> "hex_value"

size :: Parser Size
size = unsignedNumber <?> "size"

decimalBase :: Parser DecimalBase
decimalBase = decimal_base <?> "decimal_base"

binaryBase :: Parser BinaryBase
binaryBase = binary_base <?> "binary_base"

octalBase :: Parser OctalBase
octalBase = octal_base <?> "octal_base"

hexBase :: Parser HexBase
hexBase = hex_base <?> "hex_base"

unbasedUnsizedLiteral :: Parser UnbasedUnsizedLiteral
unbasedUnsizedLiteral = UnbasedUnsizedLiteral <$> (apostrophe *> unsignedNumber)
  <?> "unbased_unsized_literal"

-- | A.8.8 Strings
--
stringLiteral :: Parser StringLiteral
stringLiteral = string_lit <?> "string_literal"

-- | A.9 General
-- 
--   A.9.1 Attributes
--
attributeInstance :: Parser AttributeInstance
attributeInstance = between (lparen *> star) (star <* rparen) (attrSpec `sepBy1` comma)
  <?> "attribute_instance"

attrSpec :: Parser AttrSpec
attrSpec = AttrSpec
  <$> attrName
  <*> optional (assign_op *> constantExpression)
  <?> "attr_spec"

attrName :: Parser AttrName
attrName = identifier <?> "attr_name"

-- | A.9.2 Comments
--


-- | A.9.3 Identifiers
--

arrayIdentifier :: Parser ArrayIdentifier
arrayIdentifier = identifier <?> "array_identifier"

blockIdentifier :: Parser BlockIdentifier
blockIdentifier = identifier <?> "block_identifier"

binIdentifier :: Parser BinIdentifier
binIdentifier = identifier <?> "bin_identifier"

cellIdentifier :: Parser CellIdentifier
cellIdentifier = identifier <?> "cell_identifier"

checkerIdentifier :: Parser CheckerIdentifier
checkerIdentifier = identifier <?> "checker_identifier"

cIdentifier :: Parser CIdentifier
cIdentifier = identifier <?> "c_identifier"

classIdentifier :: Parser ClassIdentifier
classIdentifier = identifier <?> "class_identifier"

classVariableIdentifier :: Parser ClassVariableIdentifier
classVariableIdentifier = variableIdentifier <?> "class_variable_identifier"

clockingIdentifier :: Parser ClockingIdentifier
clockingIdentifier = identifier <?> "clocking_identifier"

configIdentifier :: Parser ConfigIdentifier
configIdentifier = identifier <?> "config_identifier"

constIdentifier :: Parser ConstIdentifier
constIdentifier = identifier <?> "const_identifier"

constraintIdentifier :: Parser ConstraintIdentifier
constraintIdentifier = identifier <?> "contraint_identifier"

covergroupIdentifier :: Parser CovergroupIdentifier
covergroupIdentifier = identifier <?> "covergroup_identifier"

covergroupVariableIdentifier :: Parser CovergroupVariableIdentifier
covergroupVariableIdentifier = variableIdentifier <?> "covergroup_variable_identifier"

coverPointIdentifier :: Parser CoverPointIdentifier
coverPointIdentifier = identifier <?> "cover_point_identifier"

crossIdentifier :: Parser CrossIdentifier
crossIdentifier = identifier <?> "cross_identifier"

dynamicArrayVariableIdentifier :: Parser DynamicArrayVariableIdentifier
dynamicArrayVariableIdentifier = variableIdentifier <?> "dynamic_array_variable_identifier"

enumIdentifier :: Parser EnumIdentifier
enumIdentifier = identifier <?> "enum_identifier"

formalIdentifier :: Parser FormalIdentifier
formalIdentifier = identifier <?> "formal_identifier"

formalPortIdentifier :: Parser FormalPortIdentifier
formalPortIdentifier = identifier <?> "formal_port_identifier"

functionIdentifier :: Parser FunctionIdentifier
functionIdentifier = identifier <?> "function_identifier"

generateBlockIdentifier :: Parser GenerateBlockIdentifier
generateBlockIdentifier = identifier <?> "generate_block_identifier"

genvarIdentifier :: Parser GenvarIdentifier
genvarIdentifier = identifier <?> "genvar_identifier"

hierarchicalArrayIdentifier :: Parser HierarchicalArrayIdentifier
hierarchicalArrayIdentifier = hierarchicalIdentifier <?> "hierarchical_array_identifier"

hierarchicalBlockIdentifier :: Parser HierarchicalBlockIdentifier
hierarchicalBlockIdentifier = hierarchicalIdentifier <?> "hierarchical_block_identifier"

hierarchicalEventIdentifier :: Parser HierarchicalEventIdentifier
hierarchicalEventIdentifier = hierarchicalIdentifier <?> "hierarchical_event_identifier"

hierarchicalIdentifier :: Parser HierarchicalIdentifier
hierarchicalIdentifier = HierarchicalIdentifier
  <$> optional (rootscope *> dot)
  <*> sepBy ((,) <$> identifier <*> constantBitSelect) dot
  <*> identifier
  <?> "hierarchical_identifier"

hierarchicalNetIdentifier :: Parser HierarchicalNetIdentifier
hierarchicalNetIdentifier = hierarchicalIdentifier <?> "hierarchical_net_identifier"

hierarchicalParameterIdentifier :: Parser HierarchicalParameterIdentifier
hierarchicalParameterIdentifier = hierarchicalIdentifier <?> "hierarchical_parameter_identifier"

hierarchicalPropertyIdentifier :: Parser HierarchicalPropertyIdentifier
hierarchicalPropertyIdentifier = hierarchicalIdentifier <?> "hierarchical_property_identifier"

hierarchicalSequenceIdentifier :: Parser HierarchicalSequenceIdentifier
hierarchicalSequenceIdentifier = hierarchicalIdentifier <?> "hierarchical_sequence_identifier"

hierarchicalTaskIdentifier :: Parser HierarchicalTaskIdentifier
hierarchicalTaskIdentifier = hierarchicalIdentifier <?> "hierarchical_task_identifier"

hierarchicalTfIdentifier :: Parser HierarchicalTfIdentifier
hierarchicalTfIdentifier = hierarchicalIdentifier <?> "hierarchical_tf_identifier"

hierarchicalVariableIdentifier :: Parser HierarchicalVariableIdentifier
hierarchicalVariableIdentifier = hierarchicalIdentifier <?> "hierarchical_variable_identifier"

identifier :: Parser Identifier
identifier = ident <?> "identifier"

indexVariableIdentifier :: Parser IndexVariableIdentifier
indexVariableIdentifier = identifier <?> "index_variable_identifier"

interfaceIdentifier :: Parser InterfaceIdentifier
interfaceIdentifier = identifier <?> "interface_identifier"

interfaceInstanceIdentifier :: Parser InterfaceInstanceIdentifier
interfaceInstanceIdentifier = identifier <?> "interface_intance_identifier"

inoutPortIdentifier :: Parser InoutPortIdentifier
inoutPortIdentifier = identifier <?> "inout_port_identifier"

inputPortIdentifier :: Parser InputPortIdentifier
inputPortIdentifier = identifier <?> "input_port_identifier"

instanceIdentifier :: Parser InstanceIdentifier
instanceIdentifier = identifier <?> "instance_identifier"

libraryIdentifier :: Parser LibraryIdentifier
libraryIdentifier = identifier <?> "library_identifier"

memberIdentifier :: Parser MemberIdentifier
memberIdentifier = identifier <?> "member_identifier"

methodIdentifier :: Parser MethodIdentifier
methodIdentifier = identifier <?> "method_identifier"

modportIdentifier :: Parser ModportIdentifier
modportIdentifier = identifier <?> "modport_identifier"

moduleIdentifier :: Parser ModuleIdentifier
moduleIdentifier = identifier <?> "module_identifier"

netIdentifier :: Parser NetIdentifier
netIdentifier = identifier <?> "net_identifier"

netTypeIdentifier :: Parser NetTypeIdentifier
netTypeIdentifier = identifier <?> "net_type_identifier"

outputPortIdentifier :: Parser OutputPortIdentifier
outputPortIdentifier = identifier <?> "output_port_identifier"

packageIdentifier :: Parser OutputPortIdentifier
packageIdentifier = identifier <?> "package_identifier"

packageScope :: Parser PackageScope
packageScope = Just <$> packageIdentifier <* namequal <|> Nothing <$ unitscope <* namequal
  <?> "package_scope"

parameterIdentifier :: Parser ParameterIdentifier
parameterIdentifier = identifier <?> "parameter_identifier"

portIdentifier :: Parser PortIdentifier
portIdentifier = identifier <?> "port_identifier"

productionIdentifier :: Parser ProductionIdentifier
productionIdentifier = identifier <?> "production_identifier"

programIdentifier :: Parser ProgramIdentifier
programIdentifier = identifier <?> "program_identifier"

propertyIdentifier :: Parser PropertyIdentifier
propertyIdentifier = identifier <?> "property_identifier"

psClassIdentifier :: Parser PsClassIdentifier
psClassIdentifier = PsClassIdentifier
  <$> optional packageScope
  <*> classIdentifier
  <?> "ps_class_identifier"

psCovergroupIdentifier :: Parser PsCovergroupIdentifier
psCovergroupIdentifier = PsCovergroupIdentifier
  <$> optional packageScope
  <*> covergroupIdentifier
  <?> "ps_covergroup_identifier"

psCheckerIdentifier :: Parser PsCheckerIdentifier
psCheckerIdentifier = PsCheckerIdentifier
  <$> optional packageScope
  <*> checkerIdentifier
  <?> "ps_checker_identifier"

psIdentifier :: Parser PsIdentifier
psIdentifier = PsIdentifier
  <$> optional packageScope
  <*> identifier
  <?> "ps_identifier"

psOrHierarchicalArrayIdentifier :: Parser PsOrHierarchicalArrayIdentifier
psOrHierarchicalArrayIdentifier = PsOrHierarchicalArrayIdentifier
  <$> (Left <$> implicitClassHandle <* dot <|> Right <$>
      (Left <$> classScope <|> Right <$> packageScope))
  <*> hierarchicalArrayIdentifier
  <?> "ps_or_hierarchical_array_identifier"

psOrHierarchicalNetIdentifier :: Parser PsOrHierarchicalNetIdentifier
psOrHierarchicalNetIdentifier
  =   NetIdentifier_PsOrHierarchicalNetIdentifier
      <$> optional packageScope
      <*> netIdentifier
  <|> HierarchicalNetIdentifier_PsOrHierarchicalNetIdentifier
      <$> hierarchicalNetIdentifier
  <?> "ps_or_hierarchical_net_identifier"

psOrHierarchicalPropertyIdentifier :: Parser PsOrHierarchicalPropertyIdentifier
psOrHierarchicalPropertyIdentifier
  =   PropertyIdentifier_PsOrHierarchicalPropertyIdentifier
      <$> optional packageScope
      <*> propertyIdentifier
  <|> HierarchicalPropertyIdentifier_PsOrHierarchicalPropertyIdentifier
      <$> hierarchicalPropertyIdentifier
  <?> "ps_or_hierarchical_property_identifier"

psOrHierarchicalSequenceIdentifier :: Parser PsOrHierarchicalSequenceIdentifier
psOrHierarchicalSequenceIdentifier
  =   SequenceIdentifier_PsOrHierarchicalSequenceIdentifier
      <$> optional packageScope
      <*> sequenceIdentifier
  <|> HierarchicalSequenceIdentifier_PsOrHierarchicalSequenceIdentifier
      <$> hierarchicalSequenceIdentifier
  <?> "ps_or_hierarchical_sequence_identifier"

psOrHierarchicalTfIdentifier :: Parser PsOrHierarchicalTfIdentifier
psOrHierarchicalTfIdentifier
  =   TfIdentifier_PsOrHierarchicalTfIdentifier
      <$> optional packageScope
      <*> tfIdentifier
  <|> HierarchicalTfIdentifier_PsOrHierarchicalTfIdentifier
      <$> hierarchicalTfIdentifier
  <?> "ps_or_hierarchical_tf_identifier"

psParameterIdentifier :: Parser PsParameterIdentifier
psParameterIdentifier
  =   PsParameterIdentifier
       <$> optional (Left <$> packageScope <|> Right <$> classScope)
       <*> pure []
       <*> parameterIdentifier
  <|> PsParameterIdentifier
       <$> pure Nothing
       <*> sepBy item dot
       <*> parameterIdentifier
  <?> "ps_parameter_identifier"
  where
  item = (,) <$> generateBlockIdentifier <*> optional (between lbrack rbrack constantExpression)

psTypeIdentifier :: Parser PsTypeIdentifier
psTypeIdentifier = PsTypeIdentifier
  <$> optional (Nothing <$ local <* namequal <|> Just <$> packageScope)
  <*> typeIdentifier
  <?> "ps_type_identifier"

sequenceIdentifier :: Parser SequenceIdentifier
sequenceIdentifier = identifier <?> "sequence_identifier"

signalIdentifier :: Parser SignalIdentifier
signalIdentifier = identifier <?> "signal_identifier"

simpleIdentifier :: Parser SimpleIdentifier
simpleIdentifier = identifier <?> "simple_identifier"

specparamIdentifier :: Parser SpecparamIdentifier
specparamIdentifier = identifier <?> "specparam_identifier"

systemTfIdentifier :: Parser SystemTfIdentifier
systemTfIdentifier = system_tf_identifier <?> "system_tf_identifier"

taskIdentifier :: Parser TaskIdentifier
taskIdentifier = identifier <?> "task_identifier"

tfIdentifier :: Parser TfIdentifier
tfIdentifier = identifier <?> "tf_identifier"

terminalIdentifier :: Parser TerminalIdentifier
terminalIdentifier = identifier <?> "terminal_identifier"

topmoduleIdentifier :: Parser TopmoduleIdentifier
topmoduleIdentifier = identifier <?> "topmodule_identifier"

typeIdentifier :: Parser TypeIdentifier
typeIdentifier = identifier <?> "type_identifier"

udpIdentifier :: Parser UdpIdentifier
udpIdentifier = identifier <?> "udp_identifier"

variableIdentifier :: Parser VariableIdentifier
variableIdentifier = identifier <?> "variable_identifier"


filePathSpec :: Parser FilePathSpec
filePathSpec = identifier <?> "file_path_spec"


-- | Lexer
--
maybeToken :: Monoidal a => (Token -> Maybe a) -> Parser a
maybeToken test = tokenPrim showT posT testT
  where
  showT (L _ t) = map toUpper (drop 4 (show t))
  testT (L _ t) = test t
  posT _ (L (l, c) _) ts
    = case runIdentity (uncons ts) of
        Nothing -> newPos [] l c
        Just (L (l', c') _, _) -> newPos [] l' c'
ident = maybeToken q
  where q (Tok_Ident t) = Just t; q _ = Nothing
xdigit = maybeToken q
  where q (Tok_XDigit t) = Just t; q _ = Nothing
zdigit = maybeToken q
  where q (Tok_ZDigit t) = Just t; q _ = Nothing
unsigned_number = choice [maybeToken q, octal_value, binary_value]
  where q (Tok_UnsignedNumber t) = Just t; q _ = Nothing
binary_value = maybeToken q
  where q (Tok_BinaryValue t) = Just t; q _ = Nothing
octal_value = choice [maybeToken q, binary_value]
  where q (Tok_OctalValue t) = Just t; q _ = Nothing
hex_value = choice [maybeToken q, unsigned_number, octal_value, binary_value]
  where q (Tok_HexValue t) = Just t; q _ = Nothing
decimal_base = maybeToken q
  where q (Tok_DecimalBase t) = Just t; q _ = Nothing
binary_base = maybeToken q
  where q (Tok_BinaryBase t) = Just t; q _ = Nothing
octal_base = maybeToken q
  where q (Tok_OctalBase t) = Just t; q _ = Nothing
hex_base = maybeToken q
  where q (Tok_HexBase t) = Just t; q _ = Nothing
string_lit = maybeToken q
  where q (Tok_StringLit t) = Just t; q _ = Nothing
system_tf_identifier = maybeToken q
  where q (Tok_TaskFunction t) = Just t; q _ = Nothing

p :: Token -> Parser ()
p t = maybeToken (\r -> if r == t then Just () else Nothing) <?> map toUpper (drop 4 (show t))
accept_on = p Tok_AcceptOn
alias = p Tok_Alias
always = p Tok_Always
always_latch = p Tok_AlwaysLatch
always_ff = p Tok_AlwaysFf
always_comb = p Tok_AlwaysComb
at = p Tok_At
amp = p Tok_Amp
and_ = p Tok_And
and_op = p Tok_AndOp
apostrophe = p Tok_Apos
assert = p Tok_Assert
assign = p Tok_Assign
assign_amp = p Tok_Amp
assign_shift_r = p Tok_AssShiftR
assign_shift_rr = p Tok_AssShiftRR
assign_shift_l = p Tok_AssShiftL
assign_shift_ll = p Tok_AssShiftLL
assign_caret = p Tok_AssCaret
assign_percent = p Tok_AssPercent
assign_pipe = p Tok_AssPipe
assign_slash = p Tok_AssSlash
assign_plus = p Tok_AssPlus
assign_minus = p Tok_AssMinus
assign_star = p Tok_AssStar
assume = p Tok_Assume
assign_op = p Tok_AssignOp
automatic = p Tok_Automatic
begin = p Tok_Begin
bind = p Tok_Bind
bins = p Tok_Bins
binsof = p Tok_Binsof
bit = p Tok_Bit
break_ = p Tok_Break
buf = p Tok_Buf
bufif0 = p Tok_Bufif0
bufif1 = p Tok_Bufif1
byte = p Tok_Byte
caret = p Tok_Caret
case_ = p Tok_Case
casez = p Tok_Casez
casex = p Tok_Casex
cell = p Tok_Cell
chandle = p Tok_Chandle
checker = p Tok_Checker
class_ = p Tok_Class
clocking_ = p Tok_Clocking
cmos = p Tok_Cmos
colon = p Tok_Colon
comma = p Tok_Comma
config = p Tok_Config
const_ = p Tok_Const
constraint = p Tok_Constraint
context = p Tok_Context
continue = p Tok_Continue
cross = p Tok_Cross
cover = p Tok_Cover
covergroup = p Tok_Covergroup
coverpoint = p Tok_Coverpoint
deassign = p Tok_Deassign
default_ = p Tok_Default
defparam = p Tok_Defparam
design = p Tok_Design
disable = p Tok_Disable
dist = p Tok_Dist
do_ = p Tok_Do
dot = p Tok_Dot
dollar = p Tok_Dollar
doubleat = p Tok_Doubleat
doublehash = p Tok_Doublehash
double_arrow = p Tok_DoubleArrow
dweq = p Tok_Dweq
dwne = p Tok_Dwne
edge = p Tok_Edge
else_ = p Tok_Else
end = p Tok_End
endcase = p Tok_Endcase
endchecker = p Tok_Endchecker
endclass = p Tok_Endclass
endconfig = p Tok_Endconfig
endfunction = p Tok_Endfunction
endgenerate = p Tok_Endgenerate
endgroup = p Tok_Endgroup
endinterface = p Tok_Endinterface
endmodule = p Tok_Endmodule
endpackage = p Tok_Endpackage
endprimitive = p Tok_Endprimitive
endprogram = p Tok_Endprogram
endproperty = p Tok_Endproperty
endsequence = p Tok_Endsequence
endspecify = p Tok_Specify
endtable = p Tok_Endtable
endtask = p Tok_Endtask
enum = p Tok_Enum
event = p Tok_Event
eventually = p Tok_Eventually
eq = p Tok_Eq
eq_arrow = p Tok_EqArrow
equivalent = p Tok_Equivalent
not_equivalent = p Tok_NotEquivalent
extends = p Tok_Extends
extern = p Tok_Extern
exp_ = p Tok_Exp
expect = p Tok_Expect
export = p Tok_Export
final = p Tok_Final
first_match = p Tok_FirstMatch
followed_by = p Tok_FollowedBy
followed_by_overlapped = p Tok_FollowedByOverlapped
for = p Tok_For
force = p Tok_Force
fork = p Tok_Fork
foreach = p Tok_Foreach
forever_ = p Tok_Forever
function = p Tok_Function
generate = p Tok_Generate
genvar = p Tok_Genvar
gt = p Tok_Gt
gteq = p Tok_GtEq
gtgt = p Tok_GtGt
hash = p Tok_Hash
highz0 = p Tok_Highz0
highz1 = p Tok_Highz1
if_ = p Tok_If
iff = p Tok_Iff
ifnone = p Tok_Ifnone
illegal_bins = p Tok_IllegalBins
ignore_bins = p Tok_IgnoreBins
implements = p Tok_Implements
implies = p Tok_Implies
implication = p Tok_Implication
implication_overlapped = p Tok_ImplicationOverlapped
import_ = p Tok_Import
inside = p Tok_Inside
incdir = p Tok_Incdir
include = p Tok_Include
initial = p Tok_Initial
instance_ = p Tok_Instance
interconnect = p Tok_Interconnect
intersect = p Tok_Intersect
inout = p Tok_Inout
input = p Tok_Input
int = p Tok_Int
integer = p Tok_Integer
interface = p Tok_Interface
join_ = p Tok_Join
join_any = p Tok_JoinAny
join_none = p Tok_JoinNone
large = p Tok_Large
arrow = p Tok_Arrow
let_ = p Tok_Let
local = p Tok_Local
localparam = p Tok_Localparam
logic = p Tok_Logic
lt = p Tok_Lt
lteq = p Tok_LtEq
ltlt = p Tok_LtLt
matches = p Tok_Matches
medium = p Tok_Medium
modport = p Tok_Modport
namequal = p Tok_NameQual
negedge = p Tok_Negedge
posedge = p Tok_Posedge
nettype = p Tok_Nettype
new = p Tok_New
nexttime = p Tok_Nexttime
s_nexttime = p Tok_SNexttime
nand = p Tok_Nand
nmos = p Tok_Nmos
nor = p Tok_Nor
not_ = p Tok_Not
notif0 = p Tok_Notif0
notif1 = p Tok_Notif1
not_op = p Tok_NotOp
noteq = p Tok_NotEq
output = p Tok_Output
package = p Tok_Package
parameter = p Tok_Parameter
pathpulse = p Tok_Pathpulse
plus = p Tok_Plus
pmos = p Tok_Pmos
increment = p Tok_Increment
option = p Tok_Option
or_ = p Tok_Or
or_op = p Tok_OrOp
primitive = p Tok_Primitive
program = p Tok_Program
protected = p Tok_Protected
pull0 = p Tok_Pull0
pull1 = p Tok_Pull1
pulldown = p Tok_Pulldown
pullup = p Tok_Pullup
pure_ = p Tok_Pure
randc = p Tok_Randc
randomize = p Tok_Randomize
reg = p Tok_Reg
ref = p Tok_Ref
rcmos = p Tok_Rcmos
rnmos = p Tok_Rnmos
rpmos = p Tok_Rpmos
rootscope = p Tok_Rootscope
s_always = p Tok_SAlways
s_eventually = p Tok_SEventually
s_until = p Tok_SUntil
s_until_with = p Tok_SUntilWith
static = p Tok_Static
solve = p Tok_Solve
specify = p Tok_Specify
specparam = p Tok_Specparam
std = p Tok_Std
super = p Tok_Super
lbrace = p Tok_LBrace
rbrace = p Tok_RBrace
rbrack = p Tok_RBracket
lbrack = p Tok_LBracket
lparen = p Tok_LParen
rparen = p Tok_RParen
liblist = p Tok_Liblist
library = p Tok_Library
longint = p Tok_Longint
minus = p Tok_Minus
decrement = p Tok_Decrement
module_ = p Tok_Module
macromodule = p Tok_Macromodule
null_ = p Tok_Null
question = p Tok_Question
packed = p Tok_Packed
percent = p Tok_Percent
pipe = p Tok_Pipe
priority = p Tok_Priority
property = p Tok_Property
pulsestyle_onevent = p Tok_PulsestyleOnevent
pulsestyle_ondetect = p Tok_PulsestyleOndetect
rand = p Tok_Rand
randsequence = p Tok_Randsequence
randcase = p Tok_Randcase
real = p Tok_Real
realtime = p Tok_Realtime
release = p Tok_Release
repeat_ = p Tok_Repeat
restrict = p Tok_Restrict
reject_on = p Tok_RejectOn
rtran = p Tok_Rtran
rtranif0 = p Tok_Rtranif0
rtranif1 = p Tok_Rtranif1
sample = p Tok_Sample
scalared = p Tok_Scalared
soft = p Tok_Soft
semi = p Tok_Semi
sequence__ = p Tok_Sequence
shortint = p Tok_Shortint
shortreal = p Tok_Shortreal
showcancelled = p Tok_Showcancelled
noshowcancelled = p Tok_Noshowcancelled
signed = p Tok_Signed
slash = p Tok_Slash
small = p Tok_Small
star = p Tok_Star
doublestar = p Tok_Doublestar
step1 = p Tok_1Step
string = p Tok_String
strong = p Tok_Strong
strong0 = p Tok_Strong0
strong1 = p Tok_Strong1
struct = p Tok_Struct
supply0 = p Tok_Supply0
supply1 = p Tok_Supply1
sync_accept_on = p Tok_SyncAcceptOn
sync_reject_on = p Tok_SyncRejectOn
table = p Tok_Table
tagged = p Tok_Tagged
task = p Tok_Task
tf_nochange = p Tok_TfNochange
tf_period = p Tok_TfPeriod
tf_fullskew = p Tok_TfFullskew
tf_timeskew = p Tok_TfTimeskew
tf_skew = p Tok_TfSkew
tf_recrem = p Tok_TfRecrem
tf_removal = p Tok_TfRemoval
tf_recovery = p Tok_TfRecovery
tf_setuphold = p Tok_TfSetuphold
tf_hold = p Tok_TfHold
tf_setup = p Tok_TfSetup
throughout = p Tok_Throughout
this = p Tok_This
tilde = p Tok_Tilde
time = p Tok_Time
timeprecision = p Tok_Timeprecision
timeunit = p Tok_Timeunit
tran = p Tok_Tran
tranif0 = p Tok_Tranif0
tranif1 = p Tok_Tranif1
tri0 = p Tok_Tri0
tri1 = p Tok_Tri1
triple_amp = p Tok_TripleAmp
trireg = p Tok_Trireg
trior = p Tok_Trior
tri = p Tok_Tri
triand = p Tok_Triand
type_ = p Tok_Type
type_option = p Tok_TypeOption
typedef = p Tok_Typedef
unique = p Tok_Unique
unique0 = p Tok_Unique0
unsigned = p Tok_Unsigned
use = p Tok_Use
union = p Tok_Union
unitscope = p Tok_Unitscope
until_ = p Tok_Until
until_with = p Tok_UntilWith
untyped = p Tok_Untyped
uwire = p Tok_Uwire
var = p Tok_Var
vectored = p Tok_Vectored
virtual_ = p Tok_Virtual
void_ = p Tok_Void
while_ = p Tok_While
wor = p Tok_Wor
wand = p Tok_Wand
wait = p Tok_Wait
wait_order = p Tok_WaitOrder
weak = p Tok_Weak
weak0 = p Tok_Weak0
weak1 = p Tok_Weak1
wildcard = p Tok_Wildcard
wire = p Tok_Wire
with = p Tok_With
within = p Tok_Within
xnor = p Tok_Xnor
xor = p Tok_Xor

