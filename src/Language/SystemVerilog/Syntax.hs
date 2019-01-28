
module Language.SystemVerilog.Syntax where

import Data.Text (Text)

data AST
  = LibraryText_AST LibraryText
  | SourceText_AST SourceText
  deriving (Eq, Show)

-- | A.1 Source text
--
--   A.1.1 Library source text
--
data LibraryText = LibraryText [LibraryDescription]
  deriving (Eq, Show)

data LibraryDescription
  = LibraryDeclaration_LibraryDescription LibraryDeclaration
  | IncludeStatement_LibraryDescription IncludeStatement
  | ConfigDeclaration_LibraryDescription ConfigDeclaration
  | NoLibraryDescription
  deriving (Eq, Show)

data LibraryDeclaration
  = LibraryDeclaration LibraryIdentifier [FilePathSpec] (Maybe [FilePathSpec])
  deriving (Eq, Show)

data IncludeStatement = IncludeStatement FilePathSpec
  deriving (Eq, Show)

-- | A.1.2 SystemVerilog source text
--
data SourceText = SourceText (Maybe TimeunitsDeclaration) [Description]
  deriving (Eq, Show)

data Description
  = ModuleDeclaration_Description ModuleDeclaration
  | UdpDeclaration_Description UdpDeclaration
  | InterfaceDeclaration_Description InterfaceDeclaration
  | ProgramDeclaration_Description ProgramDeclaration
  | PackageDeclaration_Description PackageDeclaration
  | PackageItem_Description [AttributeInstance] PackageItem
  | BindDirective_Description [AttributeInstance] BindDirective
  | ConfigDeclaration_Description ConfigDeclaration
  deriving (Eq, Show)

data ModuleNonAnsiHeader = ModuleNonAnsiHeader
  [AttributeInstance]
  ModuleKeyword (Maybe Lifetime) ModuleIdentifier
  [PackageImportDeclaration] (Maybe ParameterPortList) ListOfPorts
  deriving (Eq, Show)
  
data ModuleAnsiHeader = ModuleAnsiHeader
  [AttributeInstance]
  ModuleKeyword (Maybe Lifetime) ModuleIdentifier
  [PackageImportDeclaration] (Maybe ParameterPortList) (Maybe ListOfPortDeclarations)
  deriving (Eq, Show)

data ModuleDeclaration
  = ModuleNonAnsiHeader_ModuleDeclaration
    ModuleNonAnsiHeader (Maybe TimeunitsDeclaration) [ModuleItem] (Maybe ModuleIdentifier)
  | ModuleAnsiHeader_ModuleDeclaration
    ModuleAnsiHeader (Maybe TimeunitsDeclaration) [NonPortModuleItem] (Maybe ModuleIdentifier)
  | ModuleDeclaration
    [AttributeInstance] ModuleKeyword (Maybe Lifetime) ModuleIdentifier
    (Maybe TimeunitsDeclaration) [ModuleItem] (Maybe ModuleIdentifier)
  | ExternModuleNonAnsiHeader_ModuleDeclaration ModuleNonAnsiHeader
  | ExternModuleAnsiHeader_ModuleDeclaration ModuleAnsiHeader
  deriving (Eq, Show)

data ModuleKeyword = Module | Macromodule
  deriving (Eq, Show)


data InterfaceDeclaration
  = InterfaceNonAnsiHeader_InterfaceDeclaration
    InterfaceNonAnsiHeader (Maybe TimeunitsDeclaration) [InterfaceItem] (Maybe InterfaceIdentifier)
  | InterfaceAnsiHeader_InterfaceDeclaration
    InterfaceAnsiHeader (Maybe TimeunitsDeclaration) [NonPortInterfaceItem]
    (Maybe InterfaceIdentifier)
  | InterfaceDeclaration
    [AttributeInstance] InterfaceIdentifier
    (Maybe TimeunitsDeclaration) [InterfaceItem] (Maybe InterfaceIdentifier)
  | ExternInterfaceNonAnsiHeader_InterfaceDeclaration InterfaceNonAnsiHeader
  | ExternInterfaceAnsiHeader_InterfaceDeclaration InterfaceAnsiHeader
  deriving (Eq, Show)

data InterfaceNonAnsiHeader = InterfaceNonAnsiHeader
  [AttributeInstance] (Maybe Lifetime) InterfaceIdentifier [PackageImportDeclaration]
  (Maybe ParameterPortList) ListOfPorts
  deriving (Eq, Show)

data InterfaceAnsiHeader = InterfaceAnsiHeader
  [AttributeInstance] (Maybe Lifetime) InterfaceIdentifier [PackageImportDeclaration]
  (Maybe ParameterPortList) (Maybe ListOfPortDeclarations)
  deriving (Eq, Show)


data ProgramDeclaration
  = ProgramNonAnsiHeader_ProgramDeclaration
    ProgramNonAnsiHeader (Maybe TimeunitsDeclaration) [ProgramItem] (Maybe ProgramIdentifier)
  | ProgramAnsiHeader_ProgramDeclaration
    ProgramAnsiHeader (Maybe TimeunitsDeclaration) [NonPortProgramItem] (Maybe ProgramIdentifier)
  | ProgramDeclaration
    [AttributeInstance] ProgramIdentifier
    (Maybe TimeunitsDeclaration) [ProgramItem] (Maybe ProgramIdentifier)
  | ExternProgramNonAnsiHeader_ProgramDeclaration ProgramNonAnsiHeader
  | ExternProgramAnsiHeader_ProgramDeclaration ProgramAnsiHeader
  deriving (Eq, Show)

data ProgramNonAnsiHeader = ProgramNonAnsiHeader
  [AttributeInstance] (Maybe Lifetime) ProgramIdentifier [PackageImportDeclaration]
  (Maybe ParameterPortList) ListOfPorts
  deriving (Eq, Show)

data ProgramAnsiHeader = ProgramAnsiHeader
  [AttributeInstance] (Maybe Lifetime) ProgramIdentifier [PackageImportDeclaration]
  (Maybe ParameterPortList) (Maybe ListOfPortDeclarations)
  deriving (Eq, Show)


data CheckerDeclaration = CheckerDeclaration
  Identifier (Maybe (Maybe CheckerPortList))
  [([AttributeInstance], CheckerOrGenerateItem)]
  (Maybe CheckerIdentifier)
  deriving (Eq, Show)


data ClassDeclaration = ClassDeclaration
  (Maybe ()) (Maybe Lifetime) ClassIdentifier
  (Maybe ParameterPortList)
  (Maybe (ClassType, Maybe ListOfArguments))
  (Maybe [InterfaceClassType])
  [ClassItem]
  (Maybe ClassIdentifier)
  deriving (Eq, Show)

data InterfaceClassType = InterfaceClassType PsClassIdentifier (Maybe ParameterValueAssignment)
  deriving (Eq, Show)

data InterfaceClassDeclaration = InterfaceClassDeclaration
  ClassIdentifier (Maybe ParameterPortList) (Maybe [InterfaceClassType])
  [InterfaceClassItem]
  (Maybe ClassIdentifier)
  deriving (Eq, Show)

data InterfaceClassItem
  = TypeDeclaration_InterfaceClassItem TypeDeclaration
  | InterfaceClassMethod_InterfaceClassItem [AttributeInstance] InterfaceClassMethod
  | LocalParameterDeclaration_InterfaceClassItem LocalParameterDeclaration
  | ParameterDeclaration_InterfaceClassItem ParameterDeclaration
  | NoInterfaceClassItem
  deriving (Eq, Show)

data InterfaceClassMethod = InterfaceClassMethod MethodPrototype
  deriving (Eq, Show)

data PackageDeclaration = PackageDeclaration
  [AttributeInstance] (Maybe Lifetime) PackageIdentifier (Maybe TimeunitsDeclaration)
  [([AttributeInstance], PackageItem)]
  (Maybe PackageIdentifier)
  deriving (Eq, Show)

data TimeunitsDeclaration = TimeunitsDeclaration (Maybe TimeLiteral) (Maybe TimeLiteral)
  deriving (Eq, Show)


-- | A.1.3 Module parameters and ports
--
data ParameterPortList = ParameterPortList (Maybe [ParamAssignment]) [ParameterPortDeclaration]
  deriving (Eq, Show)

data ParameterPortDeclaration
  = ParameterDeclaration_ParameterPortDeclaration ParameterDeclaration
  | LocalParameterDeclaration_ParameterPortDeclaration LocalParameterDeclaration
  | DataType_ParameterPortDeclaration DataType [ParamAssignment]
  | TypeAssignments_ParameterPortDeclaration [TypeAssignment]
  deriving (Eq, Show)

type ListOfPorts = [Port]

type ListOfPortDeclarations = Maybe [([AttributeInstance], AnsiPortDeclaration)]

data PortDeclaration
  = InoutDeclaration_PortDeclaration [AttributeInstance] InoutDeclaration
  | InputDeclaration_PortDeclaration [AttributeInstance] InputDeclaration
  | OutputDeclaration_PortDeclaration [AttributeInstance] OutputDeclaration
  | RefDeclaration_PortDeclaration [AttributeInstance] RefDeclaration
  | InterfacePortDeclaration_PortDeclaration [AttributeInstance] InterfacePortDeclaration
  deriving (Eq, Show)

data Port = Port (Maybe PortIdentifier) (Maybe [PortReference])
  deriving (Eq, Show)

data PortReference = PortReference PortIdentifier ConstantSelect
  deriving (Eq, Show)

data PortDirection = Inout | Input | Output | Ref
  deriving (Eq, Show)

data NetPortHeader = NetPortHeader (Maybe PortDirection) NetPortType
  deriving (Eq, Show)

data VariablePortHeader = VariablePortHeader (Maybe PortDirection) VariablePortType
  deriving (Eq, Show)

data InterfacePortHeader = InterfacePortHeader (Maybe InterfaceIdentifier) (Maybe ModportIdentifier)
  deriving (Eq, Show)

data AnsiPortDeclaration
  = NetPortHeader_AnsiPortDeclaration (Maybe NetPortHeader) PortIdentifier
    [UnpackedDimension] (Maybe ConstantExpression)
  | InterfacePortHeader_AnsiPortDeclaration (Maybe InterfacePortHeader) PortIdentifier
    [UnpackedDimension] (Maybe ConstantExpression)
  | VariablePortHeader_AnsiPortDeclaration (Maybe VariablePortHeader) PortIdentifier
    [VariableDimension] (Maybe ConstantExpression)
  | AnsiPortDeclaration (Maybe PortDirection) PortIdentifier (Maybe Expression)
  deriving (Eq, Show)


-- | A.1.4 Module items
--
data ElaborationSystemTask
  = Fatal (Maybe (FinishNumber, Maybe ListOfArguments))
  | Error (Maybe (Maybe ListOfArguments))
  | Warning (Maybe (Maybe ListOfArguments))
  | Info (Maybe (Maybe ListOfArguments))
  deriving (Eq, Show)

type FinishNumber = Text

data ModuleCommonItem
  = ModuleOrGenerateItemDeclaration_ModuleCommonItem ModuleOrGenerateItemDeclaration
  | InterfaceInstantiation_ModuleCommonItem InterfaceInstantiation
  | ProgramInstantiation_ModuleCommonItem ProgramInstantiation
  | AssertionItem_ModuleCommonItem AssertionItem
  | BindDirective_ModuleCommonItem BindDirective
  | ContinuousAssign_ModuleCommonItem ContinuousAssign
  | NetAlias_ModuleCommonItem NetAlias
  | InitialConstruct_ModuleCommonItem InitialConstruct
  | FinalConstruct_ModuleCommonItem FinalConstruct
  | AlwaysConstruct_ModuleCommonItem AlwaysConstruct
  | LoopGenerateConstruct_ModuleCommonItem LoopGenerateConstruct
  | ConditionalGenerateConstruct_ModuleCommonItem ConditionalGenerateConstruct
  | ElaborationSystemTask_ModuleCommonItem ElaborationSystemTask
  deriving (Eq, Show)

data ModuleItem
  = PortDeclaration_ModuleItem PortDeclaration
  | NonPortModuleItem_ModuleItem NonPortModuleItem
  deriving (Eq, Show)

data ModuleOrGenerateItem
  = ParameterOverride_ModuleOrGenerateItem [AttributeInstance] ParameterOverride
  | GateInstantiation_ModuleOrGenerateItem [AttributeInstance] GateInstantiation
  | UdpInstantiation_ModuleOrGenerateItem [AttributeInstance] UdpInstantiation
  | ModuleInstantiation_ModuleOrGenerateItem [AttributeInstance] ModuleInstantiation
  | ModuleCommonItem_ModuleOrGenerateItem [AttributeInstance] ModuleCommonItem
  deriving (Eq, Show)

data ModuleOrGenerateItemDeclaration
  = PackageOrGenerateItemDeclaration_ModuleOrGenerateItemDeclaration
    PackageOrGenerateItemDeclaration
  | GenvarDeclaration_ModuleOrGenerateItemDeclaration GenvarDeclaration
  | ClockingDeclaration_ModuleOrGenerateItemDeclaration ClockingDeclaration
  | ClockingIdentifier_ModuleOrGenerateItemDeclaration ClockingIdentifier
  | DisableIff_ModuleOrGenerateItemDeclaration ExpressionOrDist
  deriving (Eq, Show)

data NonPortModuleItem
  = GenerateRegion_NonPortModuleItem GenerateRegion
  | ModuleOrGenerateItem_NonPortModuleItem ModuleOrGenerateItem
  | SpecifyBlock_NonPortModuleItem SpecifyBlock
  | SpecparamDeclaration_NonPortModuleItem [AttributeInstance] SpecparamDeclaration
  | ProgramDeclaration_NonPortModuleItem ProgramDeclaration
  | ModuleDeclaration_NonPortModuleItem ModuleDeclaration
  | InterfaceDeclaration_NonPortModuleItem InterfaceDeclaration
  | TimeunitsDeclaration_NonPortModuleItem TimeunitsDeclaration
  deriving (Eq, Show)

type ParameterOverride = ListOfDefparamAssignments

data BindDirective
  = BindTargetScope_BindDirective BindTargetScope (Maybe [BindTargetInstance]) BindInstantiation
  | BindTargetInstance_BindDirective BindTargetInstance BindInstantiation
  deriving (Eq, Show)

data BindTargetScope
  = ModuleIdentifier_BindTargetScope ModuleIdentifier
  | InterfaceIdentifier_BindTargetScope InterfaceIdentifier
  deriving (Eq, Show)

data BindTargetInstance = BindTargetInstance HierarchicalIdentifier ConstantBitSelect
  deriving (Eq, Show)

type BindTargetInstanceList = [BindTargetInstance]

data BindInstantiation
  = ProgramInstantiation_BindInstantiation ProgramInstantiation
  | ModuleInstantiation_BindInstantiation ModuleInstantiation
  | InterfaceInstantiation_BindInstantiation InterfaceInstantiation
  | CheckerInstantiation_BindInstantiation CheckerInstantiation
  deriving (Eq, Show)


-- | A.1.5 Configuration source text
--
data ConfigDeclaration = ConfigDeclaration
  ConfigIdentifier [LocalParameterDeclaration] DesignStatement [ConfigRuleStatement]
  (Maybe ConfigIdentifier)
  deriving (Eq, Show)

type DesignStatement = [(Maybe LibraryIdentifier, CellIdentifier)]

data ConfigRuleStatement
  = DefaultLiblistClause_ConfigRuleStatement LiblistClause
  | InstLiblistClause_ConfigRuleStatement InstClause LiblistClause
  | InstUseClause_ConfigRuleStatement InstClause UseClause
  | CellLiblistClause_ConfigRuleStatement CellClause LiblistClause
  | CellUseClause_ConfigRuleStatement CellClause UseClause
  deriving (Eq, Show)

type InstClause = InstName

data InstName = InstName TopmoduleIdentifier [InstanceIdentifier]
  deriving (Eq, Show)

data CellClause = CellClause (Maybe LibraryIdentifier) CellIdentifier
  deriving (Eq, Show)

type LiblistClause = [LibraryIdentifier]

data UseClause
  = UseClause (Maybe LibraryIdentifier) (Maybe CellIdentifier)
    [NamedParameterAssignment] (Maybe ())
  deriving (Eq, Show)

-- | A.1.6 Interface items
--
data InterfaceOrGenerateItem
  = ModuleCommonItem_InterfaceOrGenerateItem [AttributeInstance] ModuleCommonItem
  | ModportDeclaration_InterfaceOrGenerateItem [AttributeInstance] ModportDeclaration
  | ExternTfDeclaration_InterfaceOrGenerateItem [AttributeInstance] ExternTfDeclaration
  deriving (Eq, Show)

data ExternTfDeclaration
  = MethodPrototype_ExternTfDeclaration MethodPrototype
  | TaskPrototype_ExternTfDeclaration TaskPrototype
  deriving (Eq, Show)

data InterfaceItem
  = PortDeclaration_InterfaceItem PortDeclaration
  | NonPortInterfaceItem_InterfaceItem NonPortInterfaceItem
  deriving (Eq, Show)

data NonPortInterfaceItem 
  = GenerateRegion_NonPortInterfaceItem GenerateRegion
  | InterfaceOrGenerateItem_NonPortInterfaceItem InterfaceOrGenerateItem
  | ProgramDeclaration_NonPortInterfaceItem ProgramDeclaration
  | InterfaceDeclaration_NonPortInterfaceItem InterfaceDeclaration
  | TimeunitsDeclaration_NonPortInterfaceItem TimeunitsDeclaration
  deriving (Eq, Show)


-- | A.1.7 Program items
--
data ProgramItem
  = PortDeclaration_ProgramItem PortDeclaration
  | NonPortProgramItem_ProgramItem NonPortProgramItem
  deriving (Eq, Show)

data NonPortProgramItem
  = ContinuousAssign_NonPortProgramItem [AttributeInstance] ContinuousAssign
  | ModuleOrGenerateItemDeclaration_NonPortProgramItem [AttributeInstance]
    ModuleOrGenerateItemDeclaration
  | InitialConstruct_NonPortProgramItem [AttributeInstance] InitialConstruct
  | FinalConstruct_NonPortProgramItem [AttributeInstance] FinalConstruct
  | ConcurrentAssertionItem_NonPortProgramItem [AttributeInstance] ConcurrentAssertionItem
  | TimeunitsDeclaration_NonPortProgramItem TimeunitsDeclaration
  | ProgramGenerateItem_NonPortProgramItem ProgramGenerateItem
  deriving (Eq, Show)

data ProgramGenerateItem
  = LoopGenerateConstruct_ProgramGenerateItem LoopGenerateConstruct
  | ConditionalGenerateConstruct_ProgramGenerateItem ConditionalGenerateConstruct
  | GenerateRegion_ProgramGenerateItem GenerateRegion
  | ElaborationSystemTask_ProgramGenerateItem ElaborationSystemTask
  deriving (Eq, Show)

-- | A.1.8 Checker items
--
type CheckerPortList = [CheckerPortItem]

data CheckerPortItem = CheckerPortItem
  [AttributeInstance] (Maybe PortDirection) PropertyFormalType FormalPortIdentifier
  [VariableDimension] (Maybe PropertyActualArg)
  deriving (Eq, Show)

data CheckerOrGenerateItem
  = CheckerOrGenerateItemDeclaration_CheckerOrGenerateItem CheckerOrGenerateItemDeclaration
  | InitialConstruct_CheckerOrGenerateItem InitialConstruct
  | AlwaysConstruct_CheckerOrGenerateItem AlwaysConstruct
  | FinalConstruct_CheckerOrGenerateItem FinalConstruct
  | AssertionItem_CheckerOrGenerateItem AssertionItem
  | ContinuousAssign_CheckerOrGenerateItem ContinuousAssign
  | CheckerGenerateItem_CheckerOrGenerateItem CheckerGenerateItem
  deriving (Eq, Show)

data CheckerOrGenerateItemDeclaration
  = DataDeclaration_CheckerOrGenerateItemDeclaration (Maybe RandomQualifier) DataDeclaration
  | FunctionDeclaration_CheckerOrGenerateItemDeclaration FunctionDeclaration
  | CheckerDeclaration_CheckerOrGenerateItemDeclaration CheckerDeclaration
  | AssertionItemDeclaration_CheckerOrGenerateItemDeclaration AssertionItemDeclaration
  | CovergroupDeclaration_CheckerOrGenerateItemDeclaration CovergroupDeclaration
  | OverloadDeclaration_CheckerOrGenerateItemDeclaration OverloadDeclaration
  | GenvarDeclaration_CheckerOrGenerateItemDeclaration GenvarDeclaration
  | ClockingDeclaration_CheckerOrGenerateItemDeclaration ClockingDeclaration
  | Clocking_CheckerOrGenerateItemDeclaration ClockingIdentifier
  | Disable_CheckerOrGenerateItemDeclaration ExpressionOrDist
  deriving (Eq, Show)

data CheckerGenerateItem
  = LoopGenerateConstruct_CheckerGenerateItem LoopGenerateConstruct
  | ConditionalGenerateConstruct_CheckerGenerateItem ConditionalGenerateConstruct
  | GenerateRegion_CheckerGenerateItem GenerateRegion
  | ElaborationSystemTask_CheckerGenerateItem ElaborationSystemTask
  deriving (Eq, Show)

-- | A.1.9 Class items
--
data ClassItem
  = ClassProperty_ClassItem [AttributeInstance] ClassProperty
  | ClassMethod_ClassItem [AttributeInstance] ClassMethod
  | ClassConstraint_ClassItem [AttributeInstance] ClassConstraint
  | ClassDeclaration_ClassItem [AttributeInstance] ClassDeclaration
  | CovergroupDeclaration_ClassItem [AttributeInstance] CovergroupDeclaration
  | LocalParameterDeclaration_ClassItem LocalParameterDeclaration
  | ParameterDeclaration_ClassItem ParameterDeclaration
  | NoClassItem
  deriving (Eq, Show)

data ClassProperty
  = DataDeclaration_ClassProperty [PropertyQualifier] DataDeclaration
  | ConstClassProperty [ClassItemQualifier] DataType ConstIdentifier (Maybe ConstantExpression)
  deriving (Eq, Show)

data ClassMethod
  = TaskDeclaration_ClassMethod [MethodQualifier] TaskDeclaration
  | FunctionDeclaration_ClassMethod [MethodQualifier] FunctionDeclaration
  | MethodPrototype_ClassMethod [ClassItemQualifier] MethodPrototype
  | ExternMethodPrototype_ClassMethod [MethodQualifier] MethodPrototype
  | ClassConstructorDeclaration_ClassMethod [MethodQualifier] ClassConstructorDeclaration
  | ClassConstructorPrototype_ClassMethod [MethodQualifier] ClassConstructorPrototype
  deriving (Eq, Show)

type ClassConstructorPrototype = Maybe (Maybe TfPortList)

data ClassConstraint
  = ConstraintPrototype_ClassConstraint ConstraintPrototype
  | ConstraintDeclaration_ClassConstraint ConstraintDeclaration
  deriving (Eq, Show)

data ClassItemQualifier = Static | Protected | Local
  deriving (Eq, Show)

data PropertyQualifier
  = RandomQualifier_PropertyQualifier RandomQualifier
  | ClassItemQualifier_PropertyQualifier ClassItemQualifier
  deriving (Eq, Show)

data RandomQualifier = Rand | Randc
  deriving (Eq, Show)

data MethodQualifier
  = ClassItemQualifier_MethodQualifier ClassItemQualifier
  | MethodQualifier (Maybe ())
  deriving (Eq, Show)

data MethodPrototype
  = TaskPrototype_MethodPrototype TaskPrototype
  | FunctionPrototype_MethodPrototype FunctionPrototype
  deriving (Eq, Show)

data ClassConstructorDeclaration = ClassConstructorDeclaration
  (Maybe ClassScope) (Maybe (Maybe TfPortList)) [BlockItemDeclaration]
  (Maybe (Maybe ListOfArguments)) [FunctionStatementOrNull] (Maybe ())
  deriving (Eq, Show)


-- | A.1.10 Constraints
--
data ConstraintDeclaration = ConstraintDeclaration
  (Maybe ()) ConstraintIdentifier ConstraintBlock
  deriving (Eq, Show)

type ConstraintBlock = [ConstraintBlockItem]

data ConstraintBlockItem
  = SolveBeforeList_ConstraintBlockItem SolveBeforeList SolveBeforeList
  | ConstraintExpression_ConstraintBlockItem ConstraintExpression
  deriving (Eq, Show)

type SolveBeforeList = [ConstraintPrimary]

data ConstraintPrimary
  = ConstraintPrimary (Maybe (Either ImplicitClassHandle ClassScope))
    HierarchicalIdentifier Select
  deriving (Eq, Show)

data ConstraintExpression
  = ExpressionOrDist_ConstraintExpression (Maybe ()) ExpressionOrDist
  | UniquenessConstraint_ConstraintExpression UniquenessConstraint
  | Expression_ConstraintExpression Expression ConstraintSet
  | IfElse_ConstraintExpression Expression ConstraintSet (Maybe ConstraintSet)
  | Foreach_ConstraintExpression
    PsOrHierarchicalArrayIdentifier (Maybe LoopVariables) ConstraintSet
  | ConstraintPrimary_ConstraintExpression ConstraintPrimary
  deriving (Eq, Show)

type UniquenessConstraint = [OpenRangeList]

type ConstraintSet = [ConstraintExpression]

type DistList = [DistItem]

data DistItem = DistItem ValueRange (Maybe DistWeight)
  deriving (Eq, Show)

data DistWeight = DistWeight (Either () ()) Expression
  deriving (Eq, Show)

data ConstraintPrototype = ConstraintPrototype (Maybe ConstraintPrototypeQualifier) (Maybe ())
  ConstraintIdentifier
  deriving (Eq, Show)

data Qualifier = Extern | Pure | Context
  deriving (Eq, Show)

type ConstraintPrototypeQualifier = Qualifier

data ExternConstraintDeclaration = ExternConstraintDeclaration (Maybe ()) ClassScope
  ConstraintIdentifier ConstraintBlock
  deriving (Eq, Show)

type IdentifierList = [Identifier]

-- | A.1.11 Package items
--
data PackageItem
  = PackageOrGenerateItemDeclaration_PackageItem PackageOrGenerateItemDeclaration
  | AnonymousProgram_PackageItem AnonymousProgram
  | PackageExportDeclaration_PackageItem PackageExportDeclaration
  | TimeunitsDeclaration_PackageItem TimeunitsDeclaration
  deriving (Eq, Show)

data PackageOrGenerateItemDeclaration
  = NetDeclaration_PackageOrGenerateItemDeclaration NetDeclaration
  | DataDeclaration_PackageOrGenerateItemDeclaration DataDeclaration
  | TaskDeclaration_PackageOrGenerateItemDeclaration TaskDeclaration
  | FunctionDeclaration_PackageOrGenerateItemDeclaration FunctionDeclaration
  | CheckerDeclaration_PackageOrGenerateItemDeclaration CheckerDeclaration
  | DpiImportExport_PackageOrGenerateItemDeclaration DpiImportExport
  | ExternConstraintDeclaration_PackageOrGenerateItemDeclaration ExternConstraintDeclaration
  | ClassDeclaration_PackageOrGenerateItemDeclaration ClassDeclaration
  | ClassConstructorDeclaration_PackageOrGenerateItemDeclaration ClassConstructorDeclaration
  | LocalParameterDeclaration_PackageOrGenerateItemDeclaration LocalParameterDeclaration
  | ParameterDeclaration_PackageOrGenerateItemDeclaration ParameterDeclaration
  | CovergroupDeclaration_PackageOrGenerateItemDeclaration CovergroupDeclaration
  | OverloadDeclaration_PackageOrGenerateItemDeclaration OverloadDeclaration
  | AssertionItemDeclaration_PackageOrGenerateItemDeclaration AssertionItemDeclaration
  | NoPackageOrGenerateItemDeclaration
  deriving (Eq, Show)

type AnonymousProgram = [AnonymousProgramItem]

data AnonymousProgramItem
  = TaskDeclaration_AnonymousProgramItem TaskDeclaration
  | FunctionDeclaration_AnonymousProgramItem FunctionDeclaration
  | ClassDeclaration_AnonymousProgramItem ClassDeclaration
  | CovergroupDeclaration_AnonymousProgramItem CovergroupDeclaration
  | ClassConstructorDeclaration_AnonymousProgramItem ClassConstructorDeclaration
  | NoAnonymousProgramItem
  deriving (Eq, Show)


-- | A.2 Declarations
--   
--   A.2.1 Declaration types
--   
--   A.2.1.1 Module parameter declarations
--
data LocalParameterDeclaration
  = DataTypeOrImplicit_LocalParameterDeclaration DataTypeOrImplicit ListOfParamAssignments
  | ListOfTypeAssignments_LocalParameterDeclaration ListOfTypeAssignments
  deriving (Eq, Show)

data ParameterDeclaration
  = DataTypeOrImplicit_ParameterDeclaration DataTypeOrImplicit ListOfParamAssignments
  | ListOfTypeAssignments_ParameterDeclaration ListOfTypeAssignments
  deriving (Eq, Show)

data SpecparamDeclaration = SpecparamDeclaration (Maybe PackedDimension)
  ListOfSpecparamAssignments
  deriving (Eq, Show)

-- | A.2.1.2 Port declarations
--
data InoutDeclaration = InoutDeclaration NetPortType
  ListOfPortIdentifiers
  deriving (Eq, Show)

data InputDeclaration = InputDeclaration (Either NetPortType VariablePortType)
  ListOfPortIdentifiers
  deriving (Eq, Show)

data OutputDeclaration = OutputDeclaration (Either NetPortType VariablePortType)
  ListOfPortIdentifiers
  deriving (Eq, Show)

data InterfacePortDeclaration = InterfacePortDeclaration InterfaceIdentifier
  (Maybe ModportIdentifier) ListOfInterfaceIdentifiers
  deriving (Eq, Show)

data RefDeclaration = RefDeclaration VariablePortType ListOfVariableIdentifiers
  deriving (Eq, Show)

-- | A.2.1.3 Type declarations
--
data DataDeclaration
  = DataDeclaration (Maybe ()) (Maybe ()) (Maybe Lifetime) DataTypeOrImplicit
    ListOfVariableDeclAssignments
  | TypeDeclaration_DataDeclaration TypeDeclaration
  | NetTypeDeclaration_DataDeclaration PackageImportDeclaration NetTypeDeclaration
  deriving (Eq, Show)

type PackageImportDeclaration = [PackageImportItem]
type PackageExportDeclaration = [PackageImportItem]

data PackageImportItem = PackageImportItem PackageIdentifier (Maybe Identifier)
  deriving (Eq, Show)


type GenvarDeclaration = ListOfGenvarIdentifiers

data NetDeclaration
  = NetType_NetDeclaration NetType (Maybe (Either DriveStrength ChargeStrength))
    (Maybe Vectored) DataTypeOrImplicit (Maybe Delay3) ListOfNetDeclAssignments
  | NetDeclaration NetTypeIdentifier (Maybe DelayControl)
    ListOfNetDeclAssignments
  | ImplicitDataType_NetDeclaration ImplicitDataType (Maybe DelayValue)
    (NetIdentifier, [UnpackedDimension])
    (Maybe (NetIdentifier, [UnpackedDimension]))
  deriving (Eq, Show)

data Vectored = Vectored | Scalared
  deriving (Eq, Show)

data TypeDeclaration
  = DataType_TypeDeclaration DataType TypeIdentifier [VariableDimension]
  | InterfaceInstance_TypeDeclaration InterfaceInstanceIdentifier
    ConstantBitSelect TypeIdentifier TypeIdentifier
  | TypeDeclaration (Maybe TypeKeyword) TypeIdentifier
  deriving (Eq, Show)

data TypeKeyword = Enum | Struct | Union | Class | InterfaceClass
  deriving (Eq, Show)

data NetTypeDeclaration
  = DataType_NetTypeDeclaration DataType NetTypeIdentifier
    (Maybe (Maybe (Either PackageScope ClassScope), TfIdentifier))
  | NetTypeDeclaration (Maybe (Either PackageScope ClassScope))
    NetTypeIdentifier NetTypeIdentifier
  deriving (Eq, Show)

data Lifetime = StaticLifetime | AutomaticLifetime
  deriving (Eq, Show)

-- | A.2.2 Declaration data types
--
--   A.2.2.1 Net and variable types
--
data CastingType
  = SimpleType_CastingType SimpleType
  | ConstantPrimary_CastingType ConstantPrimary
  | Signing_CastingType Signing
  | StringCastingType
  | ConstCastingType
  deriving (Eq, Show)

data DataType
  = IntegerVectorType_DataType IntegerVectorType (Maybe Signing) [PackedDimension]
  | IntegerAtomType_DataType IntegerAtomType (Maybe Signing)
  | NonIntegerType_DataType NonIntegerType
  | StructUnion_DataType StructUnion (Maybe (Maybe Signing))
    [StructUnionMember] [PackedDimension]
  | Enum_DataType (Maybe EnumBaseType) [EnumNameDeclaration] [PackedDimension]
  | StringDataType
  | ChandleDataType
  | Interface_DataType (Maybe ()) InterfaceIdentifier
    (Maybe ParameterValueAssignment) (Maybe ModportIdentifier)
  | Type_DataType (Maybe (Either ClassScope PackageScope)) TypeIdentifier [PackedDimension]
  | ClassType_DataType ClassType
  | EventDataType
  | PsCovergroup_DataType PsCovergroupIdentifier
  | TypeReference_DataType TypeReference
  deriving (Eq, Show)

data DataTypeOrImplicit
  = DataType_DataTypeOrImplicit DataType
  | ImplicitDataType_DataTypeOrImplicit ImplicitDataType
  deriving (Eq, Show)

data ImplicitDataType = ImplicitDataType (Maybe Signing) [PackedDimension]
  deriving (Eq, Show)

data EnumBaseType
  = IntegerAtomType_EnumBaseType IntegerAtomType (Maybe Signing)
  | IntegerVectorType_EnumBaseType IntegerVectorType (Maybe Signing) (Maybe PackedDimension)
  | Type_EnumBaseType TypeIdentifier (Maybe PackedDimension)
  deriving (Eq, Show)

data EnumNameDeclaration = EnumNameDeclaration
  EnumIdentifier (Maybe (IntegralNumber, Maybe IntegralNumber)) (Maybe ConstantExpression)
  deriving (Eq, Show)

type ClassScope = ClassType

data ClassType = ClassType
  PsClassIdentifier (Maybe ParameterValueAssignment)
  [(ClassIdentifier, Maybe ParameterValueAssignment)]
  deriving (Eq, Show)

data IntegerType
  = IntegerVectorType_IntegerType IntegerVectorType
  | IntegerAtomType_IntegerType IntegerAtomType
  deriving (Eq, Show)

data IntegerAtomType = TByte | TShortint | TInt | TLongint | TInteger | TTime
  deriving (Eq, Show)

data IntegerVectorType = TBit | TLogic | TReg
  deriving (Eq, Show)

data NonIntegerType = TShortreal | TReal | TRealtime
  deriving (Eq, Show)

data NetType
  = TSupply0 | TSupply1
  | Tri | Triand | Trior | Trireg | Tri0 | Tri1
  | Uwire | Wire
  | Wand | Wor
  deriving (Eq, Show)

data NetPortType
  = DataTypeOrImplicit_NetPortType (Maybe NetType) DataTypeOrImplicit
  | NetType_NetPortType NetTypeIdentifier
  | ImplicitDataType_NetPortType ImplicitDataType
  deriving (Eq, Show)

type VariablePortType = VarDataType

data VarDataType
  = DataType_VarDataType DataType
  | DataTypeOrImplicit_VarDataType DataTypeOrImplicit
  deriving (Eq, Show)

data Signing = Signed | Unsigned
  deriving (Eq, Show)

data SimpleType
  = IntegerType_SimpleType IntegerType
  | NonIntegerType_SimpleType NonIntegerType
  | PsType_SimpleType PsTypeIdentifier
  | PsParameter_SimpleType PsParameterIdentifier
  deriving (Eq, Show)

data StructUnionMember = StructUnionMember
  [AttributeInstance] (Maybe RandomQualifier) DataTypeOrVoid ListOfVariableDeclAssignments
  deriving (Eq, Show)

data DataTypeOrVoid
  = DataType_DataTypeOrVoid DataType
  | VoidDataType
  deriving (Eq, Show)

data StructUnion
  = TStruct
  | TUnion (Maybe ())
  deriving (Eq, Show)

data TypeReference
  = Expression_TypeReference Expression
  | DataType_TypeReference DataType
  deriving (Eq, Show)


-- | A.2.2.2 Strengths
--
data DriveStrength
  = Strength0_Strength1_DriveStrength Strength0 Strength1
  | Strength1_Strength0_DriveStrength Strength1 Strength0
  deriving (Eq, Show)

data Strength0 = Supply0 | Strong0 | Pull0 | Weak0 | Highz0
  deriving (Eq, Show)

data Strength1 = Supply1 | Strong1 | Pull1 | Weak1 | Highz1
  deriving (Eq, Show)

data ChargeStrength = Small | Medium | Large
  deriving (Eq, Show)

-- | A.2.2.3 Delays
--

data Delay3
  = DelayValue_Delay3 DelayValue
  | Delay3 (MintypmaxExpression, Maybe (MintypmaxExpression, Maybe MintypmaxExpression))
  deriving (Eq, Show)

data Delay2
  = DelayValue_Delay2 DelayValue
  | Delay2 (MintypmaxExpression, Maybe MintypmaxExpression)
  deriving (Eq, Show)

data DelayValue
  = UnsignedNumber_DelayValue UnsignedNumber
  | RealNumber_DelayValue RealNumber
  | PsIdentifier_DelayValue PsIdentifier
  | TimeLiteral_DelayValue TimeLiteral
  | Step1
  deriving (Eq, Show)


-- | A.2.3 Declaration lists
--

type ListOfDefparamAssignments = [DefparamAssignment]

type ListOfGenvarIdentifiers = [GenvarIdentifier]

type ListOfInterfaceIdentifiers = [(InterfaceIdentifier, [UnpackedDimension])]

type ListOfNetDeclAssignments = [NetDeclAssignment]

type ListOfParamAssignments = [ParamAssignment]

type ListOfPortIdentifiers = [(PortIdentifier, [UnpackedDimension])]

type ListOfUdpPortIdentifiers = [PortIdentifier]

type ListOfSpecparamAssignments = [SpecparamAssignment]

type ListOfTfVariableIdentifiers
  = [(PortIdentifier, [VariableDimension], Maybe Expression)]

type ListOfTypeAssignments = [TypeAssignment]

type ListOfVariableDeclAssignments = [VariableDeclAssignment]

type ListOfVariableIdentifiers = [(VariableIdentifier, [VariableDimension])]

type ListOfVariablePortIdentifiers
  = [(PortIdentifier, [VariableDimension], Maybe ConstantExpression)]

-- | A.2.4 Declaration assignments
--

data DefparamAssignment = DefparamAssignment
  HierarchicalParameterIdentifier ConstantMintypmaxExpression
  deriving (Eq, Show)

data NetDeclAssignment = NetDeclAssignment
  NetIdentifier [UnpackedDimension] (Maybe Expression)
  deriving (Eq, Show)

data ParamAssignment = ParamAssignment
  ParameterIdentifier [UnpackedDimension] (Maybe ConstantParamExpression)
  deriving (Eq, Show)

data SpecparamAssignment
  = SpecparamAssignment SpecparamIdentifier ConstantMintypmaxExpression
  | PulseControlSpecparam_SpecparamAssignment PulseControlSpecparam
  deriving (Eq, Show)

data TypeAssignment = TypeAssignment
  TypeIdentifier (Maybe DataType)
  deriving (Eq, Show)

data PulseControlSpecparam = PulseControlSpecparam
  (Maybe (SpecifyInputTerminalDescriptor, SpecifyOutputTerminalDescriptor))
  RejectLimitValue (Maybe ErrorLimitValue)
  deriving (Eq, Show)

type ErrorLimitValue = LimitValue

type RejectLimitValue = LimitValue

type LimitValue = ConstantMintypmaxExpression

data VariableDeclAssignment
  = VariableDeclAssignment
    VariableIdentifier [VariableDimension] (Maybe Expression)
  | DynamicArrayVariableIdentifier_VariableDeclAssignment
    DynamicArrayVariableIdentifier UnsizedDimension [VariableDimension] (Maybe DynamicArrayNew)
  | ClassVariableIdentifier_VariableDeclAssignment
    ClassVariableIdentifier (Maybe ClassNew)
  deriving (Eq, Show)

data ClassNew
  = ClassNew (Maybe ClassScope) (Maybe ListOfArguments)
  | Expression_ClassNew Expression
  deriving (Eq, Show)

data DynamicArrayNew = DynamicArrayNew Expression (Maybe Expression)
  deriving (Eq, Show)


-- | A.2.5 Declaration ranges
--

data UnpackedDimension
  = ConstantRange_UnpackedDimension ConstantRange
  | ConstantExpression_UnpackedDimension ConstantExpression
  deriving (Eq, Show)

data PackedDimension
  = ConstantRange_PackedDimension ConstantRange
  | UnsizedDimension_PackedDimension UnsizedDimension
  deriving (Eq, Show)

type AssociativeDimension = Maybe DataType

data VariableDimension
  = UnsizedDimension_VariableDimension UnsizedDimension
  | UnpackedDimension_VariableDimension UnpackedDimension
  | AssociativeDimension_VariableDimension AssociativeDimension
  | QueueDimension_VariableDimension QueueDimension
  deriving (Eq, Show)

type QueueDimension = Maybe ConstantExpression

type UnsizedDimension = ()


-- | A.2.6 Function declarations
--

data FunctionDataTypeOrImplicit
  = DataTypeOrVoid_FunctionDataTypeOrImplicit DataTypeOrVoid
  | ImplicitDataType_FunctionDataTypeOrImplicit ImplicitDataType
  deriving (Eq, Show)

data FunctionDeclaration = FunctionDeclaration (Maybe Lifetime) FunctionBodyDeclaration
  deriving (Eq, Show)

data FunctionBodyDeclaration = FunctionBodyDeclaration
  FunctionDataTypeOrImplicit (Maybe (Either InterfaceIdentifier ClassScope)) FunctionIdentifier
  (Maybe TfPortList) [TfItemDeclaration] [BlockItemDeclaration]
  [FunctionStatementOrNull]
  (Maybe FunctionIdentifier)
  deriving (Eq, Show)

data FunctionPrototype = FunctionPrototype DataTypeOrVoid FunctionIdentifier
  (Maybe (Maybe TfPortList))
  deriving (Eq, Show)

data DpiImportExport
  = DpiFunctionProto_DpiImportExport DpiSpecString
    (Maybe DpiFunctionImportProperty) (Maybe CIdentifier) DpiFunctionProto
  | DpiTaskProto_DpiImportExport DpiSpecString
    (Maybe DpiTaskImportProperty) (Maybe CIdentifier) DpiTaskProto
  | FunctionIdentifier_DpiImportExport DpiSpecString (Maybe CIdentifier) FunctionIdentifier
  | TaskIdentifier_DpiImportExport DpiSpecString (Maybe CIdentifier) TaskIdentifier
  deriving (Eq, Show)

type DpiSpecString = StringLiteral

type DpiFunctionImportProperty = Qualifier

type DpiTaskImportProperty = Qualifier

type DpiFunctionProto = FunctionPrototype

type DpiTaskProto = TaskPrototype


-- | A.2.7 Task declarations
--
data TaskDeclaration = TaskDeclaration (Maybe Lifetime) TaskBodyDeclaration
  deriving (Eq, Show)

data TaskBodyDeclaration = TaskBodyDeclaration
  (Maybe (Either InterfaceIdentifier ClassScope)) TaskIdentifier
  (Maybe TfPortList) [TfItemDeclaration] [BlockItemDeclaration]
  [StatementOrNull]
  (Maybe TaskIdentifier)
  deriving (Eq, Show)

data TfItemDeclaration
  = BlockItemDeclaration_TfItemDeclaration BlockItemDeclaration
  | TfPortDeclaration_TfItemDeclaration TfPortDeclaration
  deriving (Eq, Show)

type TfPortList = [TfPortItem]

data TfPortItem = TfPortItem [AttributeInstance] (Maybe TfPortDirection) (Maybe ())
  DataTypeOrImplicit (Maybe (PortIdentifier, [VariableDimension], Maybe Expression))
  deriving (Eq, Show)

data TfPortDirection
  = PortDirection_TfPortDirection PortDirection
  | ConstRef
  deriving (Eq, Show)

data TfPortDeclaration = TfPortDeclaration [AttributeInstance] TfPortDirection (Maybe ())
  DataTypeOrImplicit ListOfTfVariableIdentifiers
  deriving (Eq, Show)

data TaskPrototype = TaskPrototype TaskIdentifier (Maybe (Maybe TfPortList))
  deriving (Eq, Show)


-- | A.2.8 Block item declarations
--
data BlockItemDeclaration
  = DataDeclaration_BlockItemDeclaration [AttributeInstance] DataDeclaration
  | LocalParameterDeclaration_BlockItemDeclaration [AttributeInstance] LocalParameterDeclaration
  | ParameterDeclaration_BlockItemDeclaration [AttributeInstance] ParameterDeclaration
  | OverloadDeclaration_BlockItemDeclaration [AttributeInstance] OverloadDeclaration
  | LetDeclaration_BlockItemDeclaration [AttributeInstance] LetDeclaration
  deriving (Eq, Show)

data OverloadDeclaration = OverloadDeclaration OverloadOperator DataType
  FunctionIdentifier OverloadProtoFormals
  deriving (Eq, Show)

data OverloadOperator
  = PlusOverload  | IncrementOverload
  | MinusOverload | DecrementOverload
  | StarOverload  | DoublestarOverload
  | SlashOverload
  | PercentOverload
  | EqOverload | NotEqOverload
  | LtOverload | LtEqOverload
  | GtOverload | GtEqOverload
  | AssignOverload
  deriving (Eq, Show)

type OverloadProtoFormals = [DataType]


-- | A.2.9 Interface declarations
--

type ModportDeclaration = [ModportItem]

data ModportItem = ModportItem ModportIdentifier [ModportPortsDeclaration]
  deriving (Eq, Show)

data ModportPortsDeclaration
  = ModportSimplePortsDeclaration_ModportPortsDeclaration [AttributeInstance]
    ModportSimplePortsDeclaration
  | ModportTfPortsDeclaration_ModportPortsDeclaration [AttributeInstance]
    ModportTfPortsDeclaration
  | ModportClockingDeclaration_ModportPortsDeclaration [AttributeInstance]
    ModportClockingDeclaration
  deriving (Eq, Show)

type ModportClockingDeclaration = ClockingIdentifier

type ModportSimplePortsDeclaration = (PortDirection, [ModportSimplePort])

data ModportSimplePort = ModportSimplePort PortIdentifier (Maybe Expression)
  deriving (Eq, Show)

type ModportTfPortsDeclaration = (ImportExport, [ModportTfPort])

data ModportTfPort
  = MethodPrototype_ModportTfPort MethodPrototype
  | TfIdentifier_ModportTfPort TfIdentifier
  deriving (Eq, Show)

data ImportExport = Import | Export
  deriving (Eq, Show)


-- | A.2.10 Assertion declarations
--

data ConcurrentAssertionItem
  = ConcurrentAssertionStatement_ConcurrentAssertionItem (Maybe BlockIdentifier)
    ConcurrentAssertionStatement
  | CheckerInstantiation_ConcurrentAssertionItem CheckerInstantiation
  deriving (Eq, Show)

data ConcurrentAssertionStatement
  = AssertPropertyStatement_ConcurrentAssertionStatement AssertPropertyStatement
  | AssumePropertyStatement_ConcurrentAssertionStatement AssumePropertyStatement
  | CoverPropertyStatement_ConcurrentAssertionStatement CoverPropertyStatement
  | CoverSequenceStatement_ConcurrentAssertionStatement CoverSequenceStatement
  | RestrictPropertyStatement_ConcurrentAssertionStatement RestrictPropertyStatement
  deriving (Eq, Show)

data AssertPropertyStatement = AssertPropertyStatement PropertySpec ActionBlock
  deriving (Eq, Show)

data AssumePropertyStatement = AssumePropertyStatement PropertySpec ActionBlock
  deriving (Eq, Show)

data CoverPropertyStatement = CoverPropertyStatement PropertySpec StatementOrNull
  deriving (Eq, Show)

data ExpectPropertyStatement = ExpectPropertyStatement PropertySpec ActionBlock
  deriving (Eq, Show)

data CoverSequenceStatement = CoverSequenceStatement
  (Maybe ClockingEvent) (Maybe ExpressionOrDist) SequenceExpr StatementOrNull
  deriving (Eq, Show)

type RestrictPropertyStatement = PropertySpec

data PropertyInstance = PropertyInstance
  PsOrHierarchicalPropertyIdentifier (Maybe (Maybe PropertyListOfArguments))
  deriving (Eq, Show)

data PropertyListOfArguments = PropertyListOfArguments
  [Maybe PropertyActualArg]
  (Maybe [(Identifier, Maybe PropertyActualArg)])
  deriving (Eq, Show)

data PropertyActualArg
  = PropertyExpr_PropertyActualArg PropertyExpr
  | SequenceActualArg_PropertyActualArg SequenceActualArg
  deriving (Eq, Show)

data AssertionItemDeclaration
  = PropertyDeclaration_AssertionItemDeclaration PropertyDeclaration
  | SequenceDeclaration_AssertionItemDeclaration SequenceDeclaration
  | LetDeclaration_AssertionItemDeclaration LetDeclaration
  deriving (Eq, Show)

data PropertyDeclaration = PropertyDeclaration PropertyIdentifier
  (Maybe (Maybe PropertyPortList))
  [AssertionVariableDeclaration] 
  PropertySpec
  (Maybe PropertyIdentifier)
  deriving (Eq, Show)

type PropertyPortList = [PropertyPortItem]

data PropertyPortItem = PropertyPortItem
  [AttributeInstance] (Maybe (Maybe PropertyLvarPortDirection)) PropertyFormalType
  FormalPortIdentifier [VariableDimension] (Maybe PropertyActualArg)
  deriving (Eq, Show)

type PropertyLvarPortDirection = PortDirection

data PropertyFormalType
  = SequenceFormalType_PropertyFormalType SequenceFormalType
  | PropertyFormalType
  deriving (Eq, Show)

data PropertySpec = PropertySpec (Maybe ClockingEvent) (Maybe ExpressionOrDist) PropertyExpr
  deriving (Eq, Show)

data PropertyExpr
  = SequenceExpr_PropertyExpr SequenceExpr
  | StrongSequenceExpr_PropertyExpr SequenceExpr
  | WeakSequenceExpr_PropertyExpr SequenceExpr
  | PropertyExpr PropertyExpr
  | NotPropertyExpr PropertyExpr
  | OrPropertyExpr PropertyExpr PropertyExpr
  | AndPropertyExpr PropertyExpr PropertyExpr
  | ImplicationOverlappedPropertyExpr SequenceExpr PropertyExpr
  | ImplicationPropertyExpr SequenceExpr PropertyExpr
  | IfElsePropertyExpr ExpressionOrDist PropertyExpr (Maybe PropertyExpr)
  | CasePropertyExpr ExpressionOrDist [PropertyCaseItem]
  | FollowedByOverlappedPropertyExpr SequenceExpr PropertyExpr
  | FollowedByPropertyExpr SequenceExpr PropertyExpr
  | NexttimePropertyExpr (Maybe ConstantExpression) PropertyExpr
  | SNexttimePropertyExpr (Maybe ConstantExpression) PropertyExpr
  | AlwaysPropertyExpr (Maybe CycleDelayConstRangeExpression) PropertyExpr
  | SAlwaysPropertyExpr ConstantRange PropertyExpr
  | SEventuallyPropertyExpr (Maybe CycleDelayConstRangeExpression) PropertyExpr
  | EventuallyPropertyExpr ConstantRange PropertyExpr
  | UntilPropertyExpr PropertyExpr PropertyExpr
  | SUntilPropertyExpr PropertyExpr PropertyExpr
  | UntilWithPropertyExpr PropertyExpr PropertyExpr
  | SUntilWithPropertyExpr PropertyExpr PropertyExpr
  | ImpliesPropertyExpr PropertyExpr PropertyExpr
  | IffPropertyExpr PropertyExpr PropertyExpr
  | AcceptOnPropertyExpr ExpressionOrDist PropertyExpr
  | RejectOnPropertyExpr ExpressionOrDist PropertyExpr
  | SyncAcceptOnPropertyExpr ExpressionOrDist PropertyExpr
  | SyncRejectOnPropertyExpr ExpressionOrDist PropertyExpr
  | PropertyInstance_PropertyExpr PropertyInstance
  | ClockingEventPropertyExpr ClockingEvent PropertyExpr
  deriving (Eq, Show)

data PropertyCaseItem = PropertyCaseItem (Maybe [ExpressionOrDist]) PropertyExpr
  deriving (Eq, Show)

data SequenceDeclaration = SequenceDeclaration SequenceIdentifier (Maybe (Maybe SequencePortList))
  [AssertionVariableDeclaration]
  SequenceExpr
  (Maybe SequenceIdentifier)
  deriving (Eq, Show)

type SequencePortList = [SequencePortItem]

data SequencePortItem = SequencePortItem
  [AttributeInstance] (Maybe (Maybe SequenceLvarPortDirection)) SequenceFormalType
  FormalPortIdentifier [VariableDimension] (Maybe SequenceActualArg)
  deriving (Eq, Show)

type SequenceLvarPortDirection = PortDirection

data SequenceFormalType
  = DataTypeOrImplicit_SequenceFormalType DataTypeOrImplicit
  | SequenceFormalType
  | UntypedFormalType
  deriving (Eq, Show)

data SequenceExpr
  = SequenceExpr (Maybe SequenceExpr) [(CycleDelayRange, SequenceExpr)]
  | ExpressionOrDist_SequenceExpr ExpressionOrDist (Maybe BooleanAbbrev)
  | SequenceInstance_SequenceExpr SequenceInstance (Maybe SequenceAbbrev)
  | SequenceMatchList_SequenceExpr SequenceExpr (Maybe [SequenceMatchItem]) (Maybe SequenceAbbrev)
  | AndSequenceExpr SequenceExpr SequenceExpr
  | IntersectSequenceExpr SequenceExpr SequenceExpr
  | OrSequenceExpr SequenceExpr SequenceExpr
  | FirstMatchSequenceExpr SequenceExpr (Maybe [SequenceMatchItem])
  | ThroughoutSequenceExpr ExpressionOrDist SequenceExpr
  | WithinSequenceExpr SequenceExpr SequenceExpr
  | ClockingEventSequenceExpr ClockingEvent SequenceExpr
  deriving (Eq, Show)

data CycleDelayRange
  = ConstantPrimary_CycleDelayRange ConstantPrimary
  | CycleDelayConstRangeExpression_CycleDelayRange CycleDelayConstRangeExpression
  | StarCycleDelayRange
  | PlusCycleDelayRange
  deriving (Eq, Show)

data SequenceMethodCall = SequenceMethodCall SequenceInstance MethodIdentifier
  deriving (Eq, Show)

data SequenceMatchItem
  = OperatorAssignment_SequenceMatchItem OperatorAssignment
  | IncOrDecExpression_SequenceMatchItem IncOrDecExpression
  | SubroutineCall_SequenceMatchItem SubroutineCall
  deriving (Eq, Show)

data SequenceInstance = SequenceInstance
  PsOrHierarchicalSequenceIdentifier (Maybe SequenceListOfArguments)
  deriving (Eq, Show)

data SequenceListOfArguments = SequenceListOfArguments
  [Maybe SequenceActualArg]
  (Maybe [(Identifier, Maybe SequenceActualArg)])
  deriving (Eq, Show)

data SequenceActualArg
  = EventExpression_SequenceActualArg EventExpression
  | SequenceExpr_SequenceActualArg SequenceExpr
  deriving (Eq, Show)

data BooleanAbbrev
  = ConsecutiveRepetition_BooleanAbbrev ConsecutiveRepetition
  | NonConsecutiveRepetition_BooleanAbbrev NonConsecutiveRepetition
  | GotoRepetition_BooleanAbbrev GotoRepetition
  deriving (Eq, Show)

type SequenceAbbrev = ConsecutiveRepetition

data ConsecutiveRepetition
  = ConstOrRangeExpression_ConsecutiveRepetition ConstOrRangeExpression
  | StarConsecutiveRepetition
  | PlusConsecutiveRepetition
  deriving (Eq, Show)

data NonConsecutiveRepetition = NonConsecutiveRepetition ConstOrRangeExpression
  deriving (Eq, Show)

data GotoRepetition = GotoRepetition ConstOrRangeExpression
  deriving (Eq, Show)

data ConstOrRangeExpression
  = ConstantExpression_ConstOrRangeExpression ConstantExpression
  | CycleDelayConstRangeExpression_ConstOrRangeExpression CycleDelayConstRangeExpression
  deriving (Eq, Show)

data CycleDelayConstRangeExpression = CycleDelayConstRangeExpression
  ConstantExpression (Maybe ConstantExpression)
  deriving (Eq, Show)

data ExpressionOrDist = ExpressionOrDist Expression (Maybe DistList)
  deriving (Eq, Show)

data AssertionVariableDeclaration = AssertionVariableDeclaration
  VarDataType ListOfVariableDeclAssignments
  deriving (Eq, Show)

data LetDeclaration = LetDeclaration
  LetIdentifier (Maybe (Maybe LetPortList)) Expression
  deriving (Eq, Show)

type LetIdentifier = Identifier

type LetPortList = [LetPortItem]

data LetPortItem = LetPortItem
  [AttributeInstance] LetFormalType FormalPortIdentifier [VariableDimension] (Maybe Expression)
  deriving (Eq, Show)

data LetFormalType
  = DataTypeOrImplicit_LetFormalType DataTypeOrImplicit
  | UntypedLetFormalType
  deriving (Eq, Show)

data LetExpression = LetExpression
  (Maybe PackageScope) LetIdentifier (Maybe (Maybe LetListOfArguments))
  deriving (Eq, Show)

data LetListOfArguments = LetListOfArguments
  [Maybe LetActualArg]
  (Maybe [(Identifier, Maybe LetActualArg)])
  deriving (Eq, Show)

type LetActualArg = Expression


-- | A.2.11 Covergroup declarations
--
data CovergroupDeclaration = CovergroupDeclaration
  CovergroupIdentifier (Maybe (Maybe TfPortList)) (Maybe CoverageEvent)
  [CoverageSpecOrOption]
  (Maybe CovergroupIdentifier)
  deriving (Eq, Show)

data CoverageSpecOrOption
  = CoverageSpec_CoverageSpecOrOption [AttributeInstance] CoverageSpec
  | CoverageOption_CoverageSpecOrOption [AttributeInstance] CoverageOption
  deriving (Eq, Show)

data CoverageOption
  = CoverageOption MemberIdentifier Expression
  | CoverageTypeOption MemberIdentifier Expression
  deriving (Eq, Show)

data CoverageSpec
  = CoverPoint_CoverageSpec CoverPoint
  | CoverCross_CoverageSpec CoverCross
  deriving (Eq, Show)

data CoverageEvent
  = ClockingEvent_CoverageEvent ClockingEvent
  | WithFunctionSample (Maybe TfPortList)
  | BlockEventExpression_CoverageEvent BlockEventExpression
  deriving (Eq, Show)

data BlockEventExpression
  = OrBlockEventExpression BlockEventExpression BlockEventExpression
  | BeginBlockEvent HierarchicalBtfIdentifier
  | EndBlockEvent HierarchicalBtfIdentifier
  deriving (Eq, Show)

data HierarchicalBtfIdentifier
  = HierarchicalTfIdentifier_HierarchicalBtfIdentifier HierarchicalTfIdentifier
  | HierarchicalBlockIdentifier_HierarchicalBtfIdentifier HierarchicalBlockIdentifier
  | MethodIdentifier_HierarchicalBtfIdentifier
    (Maybe (Either HierarchicalIdentifier ClassScope)) MethodIdentifier
  deriving (Eq, Show)

data CoverPoint = CoverPoint
  (Maybe (Maybe DataTypeOrImplicit, CoverPointIdentifier)) Expression (Maybe Expression)
  BinsOrEmpty
  deriving (Eq, Show)

type BinsOrEmpty = Maybe ([AttributeInstance], [BinsOrOptions])

data BinsOrOptions
  = CoverageOption_BinsOrOptions CoverageOption
  | CovergroupRangeList_BinsOrOptions (Maybe ())
    BinsKeyword BinIdentifier (Maybe (Maybe CovergroupExpression))
    CovergroupRangeList (Maybe CovergroupExpression)
    (Maybe Expression)
  | CoverPointIdentifier_BinsOrOptions (Maybe ())
    BinsKeyword BinIdentifier (Maybe (Maybe CovergroupExpression))
    CoverPointIdentifier (Maybe CovergroupExpression)
    (Maybe Expression)
  | SetCovergroupExpression_BinsOrOptions (Maybe ())
    BinsKeyword BinIdentifier (Maybe (Maybe CovergroupExpression))
    SetCovergroupExpression (Maybe Expression)
  | TransList_BinsOrOptions (Maybe ()) 
    BinsKeyword BinIdentifier (Maybe ()) TransList (Maybe Expression)
  | DefaultBinsOrOptions BinsKeyword BinIdentifier (Maybe (Maybe CovergroupExpression))
    (Maybe Expression)
  | DefaultSequenceBinsOrOptions BinsKeyword BinIdentifier (Maybe Expression)
  deriving (Eq, Show)
 
data BinsKeyword = Bins | IllegalBins | IgnoreBins
  deriving (Eq, Show)

type TransList = [TransSet]

type TransSet = [TransRangeList]

data TransRangeList
  = TransItem TransItem
  | TransItemStar TransItem RepeatRange
  | TransItemArrow TransItem RepeatRange
  | TransItemAssign TransItem RepeatRange
  deriving (Eq, Show)

type TransItem = CovergroupRangeList

data RepeatRange = RepeatRange CovergroupExpression (Maybe CovergroupExpression)
  deriving (Eq, Show)

data CoverCross = CoverCross (Maybe CrossIdentifier) ListOfCrossItems (Maybe Expression) CrossBody
  deriving (Eq, Show)

type ListOfCrossItems = [CrossItem]

data CrossItem
  = CoverPointIdentifier_CrossItem CoverPointIdentifier
  | VariableIdentifier_CrossItem VariableIdentifier
  deriving (Eq, Show)

type CrossBody = [CrossBodyItem]

data CrossBodyItem
  = FunctionDeclaration_CrossBodyItem FunctionDeclaration
  | BinsSelectionOrOption_CrossBodyItem BinsSelectionOrOption
  deriving (Eq, Show)

data BinsSelectionOrOption
  = CoverageOption_BinsSelectionOrOption [AttributeInstance] CoverageOption
  | BinsSelection_BinsSelectionOrOption [AttributeInstance] BinsSelection
  deriving (Eq, Show)

data BinsSelection = BinsSelection BinsKeyword BinIdentifier SelectExpression (Maybe Expression)
  deriving (Eq, Show)

data SelectExpression
  = SelectCondition SelectCondition
  | NotSelectCondition SelectCondition
  | AndSelectExpression SelectExpression SelectExpression
  | OrSelectExpression SelectExpression SelectExpression
  | SelectExpression SelectExpression
  | WithCovergroupExpression SelectExpression WithCovergroupExpression
    (Maybe IntegerCovergroupExpression)
  | CrossIdentifier_SelectExpression CrossIdentifier
  | CrossSetExpression_SelectExpression CrossSetExpression (Maybe IntegerCovergroupExpression)
  deriving (Eq, Show)

type SelectCondition = (BinsExpression, Maybe CovergroupRangeList)

data BinsExpression
  = VariableIdentifier_BinsExpression VariableIdentifier
  | CoverpointIdentifier_BinsExpression CoverPointIdentifier (Maybe BinIdentifier)
  deriving (Eq, Show)

type CovergroupRangeList = [CovergroupValueRange]

data CovergroupValueRange = CovergroupValueRange CovergroupExpression (Maybe CovergroupExpression)
  deriving (Eq, Show)

type WithCovergroupExpression = CovergroupExpression

type SetCovergroupExpression = CovergroupExpression

type IntegerCovergroupExpression = CovergroupExpression

type CrossSetExpression = CovergroupExpression

type CovergroupExpression = Expression


-- | A.3 Primitive instances
--
--   A.3.1 Primitive instantiation and instances
--

data GateInstantiation
  = CmosSwitchInstanceList_GateInstantiation CmosSwitchtype (Maybe Delay3)
    [CmosSwitchInstance]
  | EnableGateInstanceList_GateInstantiation EnableGatetype (Maybe DriveStrength) (Maybe Delay3)
    [EnableGateInstance]
  | MosSwitchInstanceList_GateInstantiation MosSwitchtype (Maybe Delay3)
    [MosSwitchInstance]
  | NInputGateInstanceList_GateInstantiation NInputGatetype (Maybe DriveStrength) (Maybe Delay2)
    [NInputGateInstance]
  | NOutputGateInstanceList_GateInstantiation NOutputGatetype (Maybe DriveStrength) (Maybe Delay2)
    [NOutputGateInstance]
  | PassEnableSwitchInstanceList_GateInstantiation PassEnSwitchtype (Maybe Delay2)
    [PassEnableSwitchInstance]
  | PassSwitchInstanceList_GateInstantiation PassSwitchtype
    [PassSwitchInstance]
  | PulldownGateInstanceList_GateInstantiation (Maybe PulldownStrength) [PullGateInstance]
  | PullupGateInstanceList_GateInstantiation (Maybe PullupStrength) [PullGateInstance]
  deriving (Eq, Show)

data CmosSwitchInstance = CmosSwitchInstance (Maybe NameOfInstance)
  (OutputTerminal, InputTerminal, NControlTerminal, PControlTerminal)
  deriving (Eq, Show)

data EnableGateInstance = EnableGateInstance (Maybe NameOfInstance)
  (OutputTerminal, InputTerminal, EnableTerminal)
  deriving (Eq, Show)

data MosSwitchInstance = MosSwitchInstance (Maybe NameOfInstance)
  (OutputTerminal, InputTerminal, EnableTerminal)
  deriving (Eq, Show)

data NInputGateInstance = NInputGateInstance (Maybe NameOfInstance)
  (OutputTerminal, [InputTerminal])
  deriving (Eq, Show)

data NOutputGateInstance = NOutputGateInstance (Maybe NameOfInstance)
  ([OutputTerminal], InputTerminal)
  deriving (Eq, Show)

data PassSwitchInstance = PassSwitchInstance (Maybe NameOfInstance)
  (InoutTerminal, InoutTerminal)
  deriving (Eq, Show)

data PassEnableSwitchInstance = PassEnableSwitchInstance (Maybe NameOfInstance)
  (InoutTerminal, InoutTerminal, EnableTerminal)
  deriving (Eq, Show)

data PullGateInstance = PullGateInstance (Maybe NameOfInstance) OutputTerminal
  deriving (Eq, Show)


-- | A.3.2 Primitive strenghts
--

data PulldownStrength
  = Strength0_Strength1_PulldownStrength Strength0 Strength1
  | Strength1_Strength0_PulldownStrength Strength1 Strength0
  | Strength0_PulldownStrength Strength0
  deriving (Eq, Show)

data PullupStrength
  = Strength0_Strength1_PullupStrength Strength0 Strength1
  | Strength1_Strength0_PullupStrength Strength1 Strength0
  | Strength1_PullupStrength Strength1
  deriving (Eq, Show)


-- | A.3.3 Primitive terminals
--

type EnableTerminal = Expression

type InoutTerminal = NetLvalue

type InputTerminal = Expression

type NControlTerminal = Expression

type OutputTerminal = NetLvalue

type PControlTerminal = Expression


-- | A.3.4 Primitive gate and switch types
--

data CmosSwitchtype = Cmos | Rcmos
  deriving (Eq, Show)

data EnableGatetype = Bufif0 | Bufif1 | Notif0 | Notif1
  deriving (Eq, Show)

data MosSwitchtype = Nmos | Pmos | Rnmos | Rpmos
  deriving (Eq, Show)

data NInputGatetype = AndN | NandN | OrN | NorN | XorN | XnorN
  deriving (Eq, Show)

data NOutputGatetype = BufN | NotN
  deriving (Eq, Show)

data PassEnSwitchtype = Tranif0 | Tranif1 | Rtranif1 | Rtranif0
  deriving (Eq, Show)

data PassSwitchtype = Tran | Rtran
  deriving (Eq, Show)


-- | A.4 Instantiations
-- 
--   A.4.1 Instantiation
-- 
--   A.4.1.1 Module instantiation

data ModuleInstantiation = ModuleInstantiation
  ModuleIdentifier (Maybe ParameterValueAssignment) [HierarchicalInstance]
  deriving (Eq, Show)

type ParameterValueAssignment = Maybe ListOfParameterAssignments

type ListOfParameterAssignments = Either [OrderedParameterAssignment] [NamedParameterAssignment]

type OrderedParameterAssignment = ParamExpression

type NamedParameterAssignment = (ParameterIdentifier, Maybe ParamExpression)

data HierarchicalInstance = HierarchicalInstance NameOfInstance (Maybe ListOfPortConnections)
  deriving (Eq, Show)

type NameOfInstance = (InstanceIdentifier, [UnpackedDimension])

type ListOfPortConnections = Either [OrderedPortConnection] [NamedPortConnection]

type OrderedPortConnection = ([AttributeInstance], Maybe Expression)

type NamedPortConnection = ([AttributeInstance], Maybe PortIdentifier, Maybe (Maybe Expression))

-- | A.4.1.2 Interface instantiation
--

data InterfaceInstantiation = InterfaceInstantiation
  InterfaceIdentifier (Maybe ParameterValueAssignment) [HierarchicalInstance]
  deriving (Eq, Show)

-- | A.4.1.3 Program instantiation
--

data ProgramInstantiation = ProgramInstantiation
  InterfaceIdentifier (Maybe ParameterValueAssignment) [HierarchicalInstance]
  deriving (Eq, Show)

-- | A.4.1.4 Checker instantiation
--

data CheckerInstantiation = CheckerInstantiation
  PsCheckerIdentifier NameOfInstance (Maybe ListOfCheckerPortConnections)
  deriving (Eq, Show)

type ListOfCheckerPortConnections
  = Either [OrderedCheckerPortConnection] [NamedCheckerPortConnection]


type OrderedCheckerPortConnection = ([AttributeInstance], Maybe PropertyActualArg)

type NamedCheckerPortConnection
  = ([AttributeInstance], Maybe FormalPortIdentifier, Maybe (Maybe PropertyActualArg))


-- | A.4.2 Generated instantiation
--

type GenerateRegion = [GenerateItem]

data LoopGenerateConstruct = LoopGenerateConstruct
  GenvarInitialization GenvarExpression GenvarIteration
  GenerateBlock
  deriving (Eq, Show)

data GenvarInitialization = GenvarInitialization (Maybe ()) GenvarIdentifier ConstantExpression
  deriving (Eq, Show)

data GenvarIteration
  = GenvarIterationAssignment GenvarIdentifier AssignmentOperator GenvarExpression
  | GenvarIterationIncOrDec (Either IncOrDecOperator IncOrDecOperator) GenvarIdentifier
  deriving (Eq, Show)

data ConditionalGenerateConstruct
  = IfGenerateConstruct_ConditionalGenerateConstruct IfGenerateConstruct
  | CaseGenerateConstruct_ConditionalGenerateConstruct CaseGenerateConstruct
  deriving (Eq, Show)

data IfGenerateConstruct = IfGenerateConstruct
  ConstantExpression GenerateBlock (Maybe GenerateBlock)
  deriving (Eq, Show)

data CaseGenerateConstruct = CaseGenerateConstruct
  ConstantExpression [CaseGenerateItem]
  deriving (Eq, Show)

data CaseGenerateItem = CaseGenerateItem (Maybe [ConstantExpression]) GenerateBlock
  deriving (Eq, Show)

data GenerateBlock
  = GenerateItem_GenerateBlock GenerateItem
  | GenerateBlock
    (Maybe GenerateBlockIdentifier) (Maybe GenerateBlockIdentifier)
    [GenerateItem]
    (Maybe GenerateBlockIdentifier)
  deriving (Eq, Show)

data GenerateItem
  = ModuleOrGenerateItem_GenerateItem ModuleOrGenerateItem
  | InterfaceOrGenerateItem_GenerateItem InterfaceOrGenerateItem
  | CheckerOrGenerateItem_GenerateItem CheckerOrGenerateItem
  deriving (Eq, Show)


-- | A.5 UDP declaration and instantiation
--
--   A.5.1 UDP declaration

data UdpNonansiDeclaration = UdpNonansiDeclaration
  [AttributeInstance] UdpIdentifier UdpPortList
  deriving (Eq, Show)

data UdpAnsiDeclaration = UdpAnsiDeclaration
  [AttributeInstance] UdpIdentifier UdpDeclarationPortList
  deriving (Eq, Show)

data UdpDeclaration
  = UdpNonansiDeclaration_UdpDeclaration
    UdpNonansiDeclaration [UdpPortDeclaration] UdpBody
    (Maybe UdpIdentifier)
  | UdpAnsiDeclaration_UdpDeclaration
    UdpAnsiDeclaration UdpBody
    (Maybe UdpIdentifier)
  | ExternUdpNonansiDeclaration_UdpDeclaration UdpNonansiDeclaration
  | ExternUdpAnsiDeclaration_UdpDeclaration UdpAnsiDeclaration
  | UdpDeclaration
    [AttributeInstance] UdpIdentifier
    [UdpPortDeclaration]
    UdpBody
    (Maybe UdpIdentifier)
  deriving (Eq, Show)


-- | A.5.2 UDP ports
--

type UdpPortList = (OutputPortIdentifier, [InputPortIdentifier])

type UdpDeclarationPortList = (UdpOutputDeclaration, [UdpInputDeclaration])

data UdpPortDeclaration
  = UdpOutputDeclaration_UdpPortDeclaration UdpOutputDeclaration
  | UdpInputDeclaration_UdpPortDeclaration UdpInputDeclaration
  | UdpRegDeclaration_UdpPortDeclaration UdpRegDeclaration
  deriving (Eq, Show)

data UdpOutputDeclaration
  = UdpOutput [AttributeInstance] PortIdentifier
  | UdpOutputReg [AttributeInstance] PortIdentifier (Maybe ConstantExpression)
  deriving (Eq, Show)

data UdpInputDeclaration = UdpInput [AttributeInstance] ListOfUdpPortIdentifiers
  deriving (Eq, Show)

data UdpRegDeclaration = UdpReg [AttributeInstance] VariableIdentifier
  deriving (Eq, Show)


-- | A.5.3 UDP body
--

data UdpBody
  = CombinationalBody_UdpBody CombinationalBody
  | SequentialBody_UdpBody SequentialBody
  deriving (Eq, Show)
  
type CombinationalBody = [CombinationalEntry]

data CombinationalEntry = CombinationalEntry LevelInputList OutputSymbol
  deriving (Eq, Show)

data SequentialBody = SequentialBody (Maybe UdpInitialStatement) [SequentialEntry]
  deriving (Eq, Show)

data UdpInitialStatement = UdpInitialStatement OutputPortIdentifier InitVal
  deriving (Eq, Show)

type InitVal = Number

data SequentialEntry = SequentialEntry SeqInputList CurrentState NextState
  deriving (Eq, Show)

data SeqInputList
  = LevelInputList_SeqInputList LevelInputList
  | EdgeInputList_SeqInputList EdgeInputList
  deriving (Eq, Show)

type LevelInputList = [LevelSymbol]

data EdgeInputList = EdgeInputList [LevelSymbol] EdgeIndicator [LevelSymbol]
  deriving (Eq, Show)

data EdgeIndicator
  = EdgeIndicator LevelSymbol LevelSymbol
  | EdgeSymbol_EdgeIndicator EdgeSymbol
  deriving (Eq, Show)

type CurrentState = LevelSymbol

type NextState = (Maybe OutputSymbol)

type OutputSymbol = UnsignedNumber

type LevelSymbol = Either Number Identifier

type EdgeSymbol = Maybe Identifier


-- | A.5.4 UDP instantiation
-- 
data UdpInstantiation = UdpInstantiation
  UdpIdentifier (Maybe DriveStrength) (Maybe Delay2) [UdpInstance]
  deriving (Eq, Show)

data UdpInstance = UdpInstance (Maybe NameOfInstance) (OutputTerminal, [InputTerminal])
  deriving (Eq, Show)


-- | A.6 Behavioral statements
--
--   A.6.1 Continuous assignment and net alias statements
-- 

data ContinuousAssign
  = ListOfNetAssignments_ContinuousAssign (Maybe DriveStrength) (Maybe Delay3) ListOfNetAssignments
  | ListOfVariableAssignments_ContinuousAssign (Maybe DelayControl) ListOfVariableAssignments
  deriving (Eq, Show)

type ListOfNetAssignments = [NetAssignment]

type ListOfVariableAssignments = [VariableAssignment]

data NetAlias = NetAlias NetLvalue [NetLvalue]
  deriving (Eq, Show)

data NetAssignment = NetAssignment NetLvalue Expression
  deriving (Eq, Show)


-- | A.6.2 Procedural blocks and assignments
--

data InitialConstruct = InitialConstruct StatementOrNull
  deriving (Eq, Show)

data AlwaysConstruct = AlwaysConstruct AlwaysKeyword Statement
  deriving (Eq, Show)

data AlwaysKeyword = Always | AlwaysComb | AlwaysLatch | AlwaysFf
  deriving (Eq, Show)

data FinalConstruct = FinalConstruct FunctionStatement
  deriving (Eq, Show)

data BlockingAssignment
  = VariableBlockingAssignment VariableLvalue DelayOrEventControl Expression
  | NonrangeVariableBlockingAssignment NonrangeVariableLvalue DynamicArrayNew
  | SelectBlockingAssignment
    (Either ImplicitClassHandle (Either ClassScope PackageScope))
    HierarchicalVariableIdentifier
    Select ClassNew
  | OperatorAssignment_BlockingAssignment OperatorAssignment
  deriving (Eq, Show)

data OperatorAssignment = OperatorAssignment VariableLvalue AssignmentOperator Expression
  deriving (Eq, Show)

data AssignmentOperator
  = Ass
  | AssPlus
  | AssMinus
  | AssStar
  | AssSlash
  | AssPercent
  | AssAmp
  | AssPipe
  | AssCaret
  | AssShiftL
  | AssShiftR
  | AssShiftLL
  | AssShiftRR
  deriving (Eq, Show)

data NonblockingAssignment = NonblockingAssignment
  VariableLvalue (Maybe DelayOrEventControl) Expression
  deriving (Eq, Show)

data ProceduralContinuousAssignment
  = ProceduralContinuousAssign VariableAssignment
  | ProceduralContinuousDeassign VariableLvalue
  | ProceduralContinuousForceVariable VariableAssignment
  | ProceduralContinuousForceNet NetAssignment
  | ProceduralContinuousReleaseVariable VariableLvalue
  | ProceduralContinuousReleaseNet NetLvalue
  deriving (Eq, Show)

data VariableAssignment = VariableAssignment VariableLvalue Expression  
  deriving (Eq, Show)


-- | A.6.3 Parallel and sequential blocks
--

data ActionBlock
  = StatementOrNull_ActionBlock StatementOrNull
  | ElseActionBlock (Maybe Statement) StatementOrNull
  deriving (Eq, Show)

data SeqBlock = SeqBlock
  (Maybe BlockIdentifier) [BlockItemDeclaration] [StatementOrNull]
  (Maybe BlockIdentifier)
  deriving (Eq, Show)

data ParBlock = ParBlock
  (Maybe BlockIdentifier) [BlockItemDeclaration] [StatementOrNull]
  JoinKeyword (Maybe BlockIdentifier)
  deriving (Eq, Show)

data JoinKeyword = Join | JoinAny | JoinNone
  deriving (Eq, Show)


-- | A.6.4 Statements
--

data StatementOrNull
  = Statement_StatementOrNull Statement
  | Null_StatementOrNull [AttributeInstance]
  deriving (Eq, Show)

data Statement = Statement (Maybe BlockIdentifier) [AttributeInstance] StatementItem
  deriving (Eq, Show)

data StatementItem
  = BlockingAssignment_StatementItem BlockingAssignment
  | NonblockingAssignment_StatementItem NonblockingAssignment
  | ProceduralContinuousAssignment_StatementItem ProceduralContinuousAssignment
  | CaseStatement_StatementItem CaseStatement
  | ConditionalStatement_StatementItem ConditionalStatement
  | IncOrDecExpression_StatementItem IncOrDecExpression
  | SubroutineCallStatement_StatementItem SubroutineCallStatement
  | DisableStatement_StatementItem DisableStatement
  | EventTrigger_StatementItem EventTrigger
  | LoopStatement_StatementItem LoopStatement
  | JumpStatement_StatementItem JumpStatement
  | ParBlock_StatementItem ParBlock
  | ProceduralTimingControlStatement_StatementItem ProceduralTimingControlStatement
  | SeqBlock_StatementItem SeqBlock
  | WaitStatement_StatementItem WaitStatement
  | ProceduralAssertionStatement_StatementItem ProceduralAssertionStatement
  | ClockingDrive_StatementItem ClockingDrive
  | RandsequenceStatement_StatementItem RandsequenceStatement
  | RandcaseStatement_StatementItem RandcaseStatement
  | ExpectPropertyStatement_StatementItem ExpectPropertyStatement
  deriving (Eq, Show)

type FunctionStatement = Statement

data FunctionStatementOrNull
  = FunctionStatement_FunctionStatementOrNull FunctionStatement
  | Null_FunctionStatementOrNull [AttributeInstance]
  deriving (Eq, Show)

type VariableIdentifierList = [VariableIdentifier]


-- | A.6.5 Timing control statements
--

type ProceduralTimingControlStatement = (ProceduralTimingControl, StatementOrNull)

data DelayOrEventControl
  = DelayControl_DelayOrEventControl DelayControl
  | EventControl_DelayOrEventControl EventControl
  | RepeatEventControl_DelayOrEventControl Expression EventControl
  deriving (Eq, Show)

type DelayControl = Either DelayValue MintypmaxExpression

data EventControl
  = HierarchicalEventIdentifier_EventControl HierarchicalEventIdentifier
  | EventExpression_EventControl EventExpression
  | EventControl
  | PsOrHierarchicalSequenceIdentifier_EventControl PsOrHierarchicalSequenceIdentifier
  deriving (Eq, Show)

data EventExpression
  = Expression_EventExpression (Maybe EdgeIdentifier) Expression (Maybe Expression)
  | SequenceInstance_EventExpression SequenceInstance (Maybe Expression)
  | OrEventExpression EventExpression EventExpression
  | SepEventExpression EventExpression EventExpression
  | EventExpression EventExpression
  deriving (Eq, Show)

data ProceduralTimingControl
  = DelayControl_ProceduralTimingControl DelayControl
  | EventControl_ProceduralTimingControl EventControl
  | CycleDelay_ProceduralTimingControl CycleDelay
  deriving (Eq, Show)

data JumpStatement
  = Return (Maybe Expression)
  | Break
  | Continue
  deriving (Eq, Show)

data WaitStatement
  = Wait Expression StatementOrNull
  | WaitFork
  | WaitOrder [HierarchicalIdentifier] ActionBlock
  deriving (Eq, Show)

data EventTrigger
  = ArrowEventTrigger HierarchicalEventIdentifier
  | DoubleArrowEventTrigger (Maybe DelayOrEventControl) HierarchicalEventIdentifier
  deriving (Eq, Show)

data DisableStatement
  = DisableTask HierarchicalTaskIdentifier
  | DisableBlock HierarchicalBlockIdentifier
  | DisableFork
  deriving (Eq, Show)


-- | A.6.6 Conditional statements
--
data ConditionalStatement = ConditionalStatement
  (Maybe UniquePriority) CondPredicate StatementOrNull
  [(CondPredicate, StatementOrNull)]
  (Maybe StatementOrNull)
  deriving (Eq, Show)

data UniquePriority = Unique | Unique0 | Priority
  deriving (Eq, Show)

data CondPredicate = CondPredicate [ExpressionOrCondPattern]
  deriving (Eq, Show)

type ExpressionOrCondPattern = Either Expression CondPattern

data CondPattern = CondPattern Expression Pattern
  deriving (Eq, Show)


-- | A.6.7 Case statements
--
data CaseStatement
  = CaseStatement (Maybe UniquePriority) CaseKeyword CaseExpression [CaseItem]
  | CaseStatementMatches (Maybe UniquePriority) CaseKeyword CaseExpression [CasePatternItem]
  | CaseStatementInside (Maybe UniquePriority) CaseExpression [CaseInsideItem]
  deriving (Eq, Show)

data CaseKeyword = Case | Casez | Casex
  deriving (Eq, Show)

type CaseExpression = Expression

data CaseItem = CaseItem (Maybe [CaseItemExpression]) StatementOrNull
  deriving (Eq, Show)

data CasePatternItem = CasePatternItem (Maybe Pattern) (Maybe Expression) StatementOrNull
  deriving (Eq, Show)

data CaseInsideItem = CaseInsideItem (Maybe OpenRangeList) StatementOrNull
  deriving (Eq, Show)

type CaseItemExpression = Expression

data RandcaseStatement = RandcaseStatement [RandcaseItem]
  deriving (Eq, Show)

type RandcaseItem = (Expression, StatementOrNull)

type OpenRangeList = [OpenValueRange]

type OpenValueRange = ValueRange


-- | A.6.7.1 Patterns
--

data Pattern
  = VariableIdentifier_Pattern VariableIdentifier
  | WildcardPattern
  | ConstantExpression_Pattern ConstantExpression
  | TaggedPattern MemberIdentifier (Maybe Pattern)
  | PatternList_Pattern [Pattern]
  | MemberList_Pattern [(MemberIdentifier, Pattern)]
  deriving (Eq, Show)

data AssignmentPattern
  = ExpressionList_AssignmentPattern [Expression]
  | StructurePatternKeyList_AssignmentPattern [(StructurePatternKey, Expression)]
  | ArrayPatternKeyList_AssignmentPattern [(ArrayPatternKey, Expression)]
  | ConstantExpression_AssignmentPattern ConstantExpression [Expression]
  deriving (Eq, Show)

type StructurePatternKey = Either MemberIdentifier AssignmentPatternKey

type ArrayPatternKey = Either ConstantExpression AssignmentPatternKey

type AssignmentPatternKey = Maybe SimpleType

data AssignmentPatternExpression = AssignmentPatternExpression
  (Maybe AssignmentPatternExpressionType) AssignmentPattern
  deriving (Eq, Show)

data AssignmentPatternExpressionType
  = PsTypeIdentifier_AssignmentPatternExpressionType PsTypeIdentifier
  | PsParameterIdentifier_AssignmentPatternExpressionType PsParameterIdentifier
  | IntegerAtomType_AssignmentPatternExpressionType IntegerAtomType
  | TypeReference_AssignmentPatternExpressionType TypeReference
  deriving (Eq, Show)

type ConstantAssignmentPatternExpression = AssignmentPatternExpression

type AssignmentPatternNetLvalue = [NetLvalue]

type AssignmentPatternVariableLvalue = [VariableLvalue]


-- | A.6.8 Looping statements
--

data LoopStatement
  = Forever StatementOrNull
  | Repeat Expression StatementOrNull
  | While Expression StatementOrNull
  | For (Maybe ForInitialization) (Maybe Expression) (Maybe ForStep) StatementOrNull
  | DoWhile StatementOrNull Expression
  | Foreach PsOrHierarchicalArrayIdentifier LoopVariables Statement
  deriving (Eq, Show)

type ForInitialization = Either ListOfVariableAssignments [ForVariableDeclaration]

data ForVariableDeclaration = ForVariableDeclaration
  (Maybe ()) DataType [(VariableIdentifier, Expression)]
  deriving (Eq, Show)

type ForStep = [ForStepAssignment]

data ForStepAssignment
  = OperatorAssignment_ForStepAssignment OperatorAssignment
  | IncOrDecExpression_ForStepAssignment IncOrDecExpression
  | FunctionSubroutineCall_ForStepAssignment FunctionSubroutineCall
  deriving (Eq, Show)

type LoopVariables = [Maybe IndexVariableIdentifier]


-- | A.6.9 Subroutine call statements
-- 

type SubroutineCallStatement = Either SubroutineCall FunctionSubroutineCall


-- | A.6.10 Assertion statements
--

data AssertionItem
  = ConcurrentAssertionItem_AssertionItem ConcurrentAssertionItem
  | DeferredImmediateAssertionItem_AssertionItem DeferredImmediateAssertionItem
  deriving (Eq, Show)

data DeferredImmediateAssertionItem = DeferredImmediateAssertionItem
  (Maybe BlockIdentifier) DeferredImmediateAssertionStatement
  deriving (Eq, Show)

data ProceduralAssertionStatement
  = ConcurrentAssertionStatement_ProceduralAssertionStatement ConcurrentAssertionStatement
  | ImmediateAssertionStatement_ProceduralAssertionStatement ImmediateAssertionStatement
  | CheckerInstantiation_ProceduralAssertionStatement CheckerInstantiation
  deriving (Eq, Show)

data ImmediateAssertionStatement
  = SimpleImmediateAssertionStatement_ImmediateAssertionStatement
    SimpleImmediateAssertionStatement
  | DeferredImmediateAssertionStatement_ImmediateAssertionStatement
    DeferredImmediateAssertionStatement
  deriving (Eq, Show)

data SimpleImmediateAssertionStatement
  = SimpleImmediateAssertStatement_SimpleImmediateAssertionStatement SimpleImmediateAssertStatement
  | SimpleImmediateAssumeStatement_SimpleImmediateAssertionStatement SimpleImmediateAssumeStatement
  | SimpleImmediateCoverStatement_SimpleImmediateAssertionStatement SimpleImmediateCoverStatement
  deriving (Eq, Show)

data SimpleImmediateAssertStatement = SimpleImmediateAssertStatement
  Expression ActionBlock
  deriving (Eq, Show)

data SimpleImmediateAssumeStatement = SimpleImmediateAssumeStatement
  Expression ActionBlock
  deriving (Eq, Show)

data SimpleImmediateCoverStatement = SimpleImmediateCoverStatement
  Expression StatementOrNull
  deriving (Eq, Show)

data DeferredImmediateAssertionStatement
  = DeferredImmediateAssertStatement_DeferredImmediateAssertionStatement
    DeferredImmediateAssertStatement
  | DeferredImmediateAssumeStatement_DeferredImmediateAssertionStatement
    DeferredImmediateAssumeStatement
  | DeferredImmediateCoverStatement_DeferredImmediateAssertionStatement
    DeferredImmediateCoverStatement
  deriving (Eq, Show)

data DeferredImmediateAssertStatement = DeferredImmediateAssertStatement
  ZeroOrFinal Expression ActionBlock
  deriving (Eq, Show)

data DeferredImmediateAssumeStatement = DeferredImmediateAssumeStatement
  ZeroOrFinal Expression ActionBlock
  deriving (Eq, Show)

data DeferredImmediateCoverStatement = DeferredImmediateCoverStatement
  ZeroOrFinal Expression StatementOrNull
  deriving (Eq, Show)

data ZeroOrFinal = Zero | Final
  deriving (Eq, Show)


-- | 6.11 Clocking block
--

data ClockingDeclaration = ClockingDeclaration
  (Maybe ()) (Maybe ClockingIdentifier) ClockingEvent
  [ClockingItem]
  (Maybe ClockingIdentifier)
  deriving (Eq, Show)

data ClockingEvent
  = Identifier_ClockingEvent Identifier
  | EventExpression_ClockingEvent EventExpression
  deriving (Eq, Show)

data ClockingItem
  = DefaultSkew_ClockingItem DefaultSkew
  | ListOfClockingDeclAssign_ClockingItem ClockingDirection ListOfClockingDeclAssign
  | AssertionItemDeclaration_ClockingItem [AttributeInstance] AssertionItemDeclaration
  deriving (Eq, Show)

data DefaultSkew
  = InputDefaultSkew ClockingSkew
  | OutputDefaultSkew ClockingSkew
  | InputOutputDefaultSkew ClockingSkew ClockingSkew
  deriving (Eq, Show)

data ClockingDirection
  = InputClockingDirection (Maybe ClockingSkew)
  | OutputClockingDirection (Maybe ClockingSkew)
  | InputOutputClockingDirection (Maybe ClockingSkew) (Maybe ClockingSkew)
  | InoutClockingDirection
  deriving (Eq, Show)

type ListOfClockingDeclAssign = [ClockingDeclAssign]

data ClockingDeclAssign = ClockingDeclAssign SignalIdentifier (Maybe Expression)
  deriving (Eq, Show)

data ClockingSkew
  = EdgeIdentifier_ClockingSkew EdgeIdentifier (Maybe DelayControl)
  | DelayControl_ClockingSkew DelayControl
  deriving (Eq, Show)

data ClockingDrive = ClockingDrive
  ClockvarExpression (Maybe CycleDelay) Expression
  deriving (Eq, Show)

data CycleDelay
  = IntegralNumber_CycleDelay IntegralNumber
  | Identifier_CycleDelay Identifier
  | Expression_CycleDelay Expression
  deriving (Eq, Show)

type Clockvar = HierarchicalIdentifier

type ClockvarExpression = (Clockvar, Select)


-- | A.6.12 Randsequence
-- 

data RandsequenceStatement = RandsequenceStatement (Maybe ProductionIdentifier) [Production]
  deriving (Eq, Show)

data Production = Production (Maybe DataTypeOrVoid) ProductionIdentifier (Maybe TfPortList) [RsRule]
  deriving (Eq, Show)

data RsRule = RsRule RsProductionList (Maybe (WeightSpecification, Maybe RsCodeBlock))
  deriving (Eq, Show)

data RsProductionList
  = RsProds_RsProductionList [RsProd]
  | ProductionItems_RsProductionList (Maybe Expression) ProductionItem [ProductionItem]
  deriving (Eq, Show)

data WeightSpecification
  = IntegralNumber_WeightSpecification IntegralNumber
  | PsIdentifier_WeightSpecification PsIdentifier
  | Expression_WeightSpecification Expression
  deriving (Eq, Show)

data RsCodeBlock = RsCodeBlock [DataDeclaration] [StatementOrNull]
  deriving (Eq, Show)

data RsProd
  = ProductionItem_RsProd ProductionItem
  | RsCodeBlock_RsProd RsCodeBlock
  | RsIfElse_RsProd RsIfElse
  | RsRepeat_RsProd RsRepeat
  | RsCase_RsProd RsCase
  deriving (Eq, Show)

data ProductionItem = ProductionItem ProductionIdentifier (Maybe ListOfArguments)
  deriving (Eq, Show)

data RsIfElse = RsIfElse Expression ProductionItem (Maybe ProductionItem)
  deriving (Eq, Show)

data RsRepeat = RsRepeat Expression ProductionItem
  deriving (Eq, Show)

data RsCase = RsCase CaseExpression [RsCaseItem]
  deriving (Eq, Show)

data RsCaseItem = RsCaseItem (Maybe [CaseItemExpression]) ProductionItem
  deriving (Eq, Show)


-- | A.7 Specify section
--
--   A.7.1 Specify block declaration
--

data SpecifyBlock = SpecifyBlock [SpecifyItem]
  deriving (Eq, Show)

data SpecifyItem
  = SpecparamDeclaration_SpecifyItem SpecparamDeclaration
  | PulsestyleDeclaration_SpecifyItem PulsestyleDeclaration
  | ShowcancelledDeclaration_SpecifyItem ShowcancelledDeclaration
  | PathDeclaration_SpecifyItem PathDeclaration
  | SystemTimingCheck_SpecifyItem SystemTimingCheck
  deriving (Eq, Show)

data PulsestyleDeclaration
  = PulsestyleOnevent ListOfPathOutputs
  | PulsestyleOndetect ListOfPathOutputs
  deriving (Eq, Show)

data ShowcancelledDeclaration
  = Showcancelled ListOfPathOutputs
  | Noshowcancelled ListOfPathOutputs
  deriving (Eq, Show)


-- | A.7.2 Specify path declarations
--

data PathDeclaration
  = SimplePathDeclaration_PathDeclaration SimplePathDeclaration
  | EdgeSensitivePathDeclaration_PathDeclaration EdgeSensitivePathDeclaration
  | StateDependentPathDeclaration_PathDeclaration StateDependentPathDeclaration
  deriving (Eq, Show)

data SimplePathDeclaration
  = ParallelPathDescription_SimplePathDeclaration ParallelPathDescription PathDelayValue
  | FullPathDescription_SimplePathDeclaration FullPathDescription PathDelayValue
  deriving (Eq, Show)

data ParallelPathDescription = ParallelPathDescription
  SpecifyInputTerminalDescriptor (Maybe PolarityOperator) SpecifyOutputTerminalDescriptor
  deriving (Eq, Show)

data FullPathDescription = FullPathDescription
  ListOfPathInputs (Maybe PolarityOperator) ListOfPathOutputs
  deriving (Eq, Show)

type ListOfPathInputs = [SpecifyInputTerminalDescriptor]

type ListOfPathOutputs = [SpecifyOutputTerminalDescriptor]


-- | A.7.3 Specify block terminals
--

data SpecifyInputTerminalDescriptor = SpecifyInputTerminalDescriptor
  InputIdentifier (Maybe ConstantRangeExpression)
  deriving (Eq, Show)

data SpecifyOutputTerminalDescriptor = SpecifyOutputTerminalDescriptor
  OutputIdentifier (Maybe ConstantRangeExpression)
  deriving (Eq, Show)

data InputIdentifier
  = InputPortIdentifier_InputIdentifier InputPortIdentifier
  | InoutPortIdentifier_InputIdentifier InoutPortIdentifier
  | PortIdentifier_InputIdentifier InterfaceIdentifier PortIdentifier
  deriving (Eq, Show)

data OutputIdentifier
  = OutputPortIdentifier_OutputIdentifier OutputPortIdentifier
  | InoutPortIdentifier_OutputIdentifier InoutPortIdentifier
  | PortIdentifier_OutputIdentifier InterfaceIdentifier PortIdentifier
  deriving (Eq, Show)


-- | A.7.4 Specify path delays
--

data PathDelayValue = PathDelayValue ListOfPathDelayExpressions
  deriving (Eq, Show)

data ListOfPathDelayExpressions
  = TPathDelayExpression_ListOfPathDelayExpressions TPathDelayExpression
  | RiseFall TrisePathDelayExpression TfallPathDelayExpression
  | RiseFallZ TrisePathDelayExpression TfallPathDelayExpression TzPathDelayExpression
  | RiseFall01Z
    T01PathDelayExpression T10PathDelayExpression T0zPathDelayExpression
    Tz1PathDelayExpression T1zPathDelayExpression Tz0PathDelayExpression
  | RiseFall01XZ
    T01PathDelayExpression T10PathDelayExpression T0zPathDelayExpression
    Tz1PathDelayExpression T1zPathDelayExpression Tz0PathDelayExpression
    T0xPathDelayExpression Tx1PathDelayExpression T1xPathDelayExpression
    Tx0PathDelayExpression TxzPathDelayExpression TzxPathDelayExpression
  deriving (Eq, Show)
 
type TPathDelayExpression = PathDelayExpression 

type TrisePathDelayExpression = PathDelayExpression 

type TfallPathDelayExpression = PathDelayExpression 

type TzPathDelayExpression = PathDelayExpression 

type T01PathDelayExpression = PathDelayExpression 

type T10PathDelayExpression = PathDelayExpression 

type T0zPathDelayExpression = PathDelayExpression 

type Tz1PathDelayExpression = PathDelayExpression 

type T1zPathDelayExpression = PathDelayExpression 

type Tz0PathDelayExpression = PathDelayExpression 

type T0xPathDelayExpression = PathDelayExpression 

type Tx1PathDelayExpression = PathDelayExpression 

type T1xPathDelayExpression = PathDelayExpression 

type Tx0PathDelayExpression = PathDelayExpression 

type TxzPathDelayExpression = PathDelayExpression 

type TzxPathDelayExpression = PathDelayExpression 

type PathDelayExpression = ConstantMintypmaxExpression 

data EdgeSensitivePathDeclaration
  = ParallelEdgeSensitivePathDescription_EdgeSensitivePathDeclaration
    ParallelEdgeSensitivePathDescription PathDelayValue
  | FullEdgeSensitivePathDescription_EdgeSensitivePathDeclaration
    FullEdgeSensitivePathDescription PathDelayValue
  deriving (Eq, Show)

data ParallelEdgeSensitivePathDescription = ParallelEdgeSensitivePathDescription
  (Maybe EdgeIdentifier) SpecifyInputTerminalDescriptor (Maybe PolarityOperator)
  SpecifyOutputTerminalDescriptor (Maybe PolarityOperator) DataSourceExpression
  deriving (Eq, Show)

data FullEdgeSensitivePathDescription = FullEdgeSensitivePathDescription
  (Maybe EdgeIdentifier) ListOfPathInputs (Maybe PolarityOperator)
  ListOfPathOutputs (Maybe PolarityOperator) DataSourceExpression
  deriving (Eq, Show)

type DataSourceExpression = Expression

data EdgeIdentifier = Posedge | Negedge | Edge
  deriving (Eq, Show)

data StateDependentPathDeclaration
  = IfSimplePathDeclaration ModulePathExpression SimplePathDeclaration
  | IfEdgeSensitivePathDeclaration ModulePathExpression EdgeSensitivePathDeclaration
  | IfNoneSimplePathDeclaration SimplePathDeclaration
  deriving (Eq, Show)

data PolarityOperator = PlusPol | MinusPol
  deriving (Eq, Show)


-- | A.7.5 System timing checks
--
--   A.7.5.1 System timing check commands
--

data SystemTimingCheck
  = SetupTimingCheck_SystemTimingCheck SetupTimingCheck
  | HoldTimingCheck_SystemTimingCheck HoldTimingCheck
  | SetupholdTimingCheck_SystemTimingCheck SetupholdTimingCheck
  | RecoveryTimingCheck_SystemTimingCheck RecoveryTimingCheck
  | RemovalTimingCheck_SystemTimingCheck RemovalTimingCheck
  | RecremTimingCheck_SystemTimingCheck RecremTimingCheck
  | SkewTimingCheck_SystemTimingCheck SkewTimingCheck
  | TimeskewTimingCheck_SystemTimingCheck TimeskewTimingCheck
  | FullskewTimingCheck_SystemTimingCheck FullskewTimingCheck
  | PeriodTimingCheck_SystemTimingCheck PeriodTimingCheck
  | WidthTimingCheck_SystemTimingCheck WidthTimingCheck
  | NochangeTimingCheck_SystemTimingCheck NochangeTimingCheck
  deriving (Eq, Show)

data SetupTimingCheck = SetupTimingCheck
  DataEvent ReferenceEvent TimingCheckLimit (Maybe (Maybe Notifier))
  deriving (Eq, Show)

data HoldTimingCheck = HoldTimingCheck
  ReferenceEvent DataEvent TimingCheckLimit (Maybe (Maybe Notifier))
  deriving (Eq, Show)

data SetupholdTimingCheck = SetupholdTimingCheck
  ReferenceEvent DataEvent TimingCheckLimit TimingCheckLimit
  (Maybe (Maybe Notifier,
   Maybe (Maybe TimestampCondition,
   Maybe (Maybe TimecheckCondition,
   Maybe (Maybe DelayedReference, Maybe (Maybe DelayedData))))))
  deriving (Eq, Show)

data RecoveryTimingCheck = RecoveryTimingCheck
  ReferenceEvent DataEvent TimingCheckLimit (Maybe (Maybe Notifier))
  deriving (Eq, Show)

data RemovalTimingCheck = RemovalTimingCheck
  ReferenceEvent DataEvent TimingCheckLimit (Maybe (Maybe Notifier))
  deriving (Eq, Show)

data RecremTimingCheck = RecremTimingCheck
  ReferenceEvent DataEvent TimingCheckLimit TimingCheckLimit
  (Maybe (Maybe Notifier,
   Maybe (Maybe TimestampCondition,
   Maybe (Maybe TimecheckCondition,
   Maybe (Maybe DelayedReference, Maybe (Maybe DelayedData))))))
  deriving (Eq, Show)

data SkewTimingCheck = SkewTimingCheck
  ReferenceEvent DataEvent TimingCheckLimit (Maybe (Maybe Notifier))
  deriving (Eq, Show)

data TimeskewTimingCheck = TimeskewTimingCheck
  ReferenceEvent DataEvent TimingCheckLimit
  (Maybe (Maybe Notifier,
   Maybe (Maybe EventBasedFlag, Maybe (Maybe RemainActiveFlag))))
  deriving (Eq, Show)

data FullskewTimingCheck = FullskewTimingCheck
  ReferenceEvent DataEvent TimingCheckLimit TimingCheckLimit
  (Maybe (Maybe Notifier,
   Maybe (Maybe EventBasedFlag, Maybe (Maybe RemainActiveFlag))))
  deriving (Eq, Show)

data PeriodTimingCheck = PeriodTimingCheck
  ControlledReferenceEvent TimingCheckLimit (Maybe (Maybe Notifier))
  deriving (Eq, Show)

data WidthTimingCheck = WidthTimingCheck
  ControlledReferenceEvent TimingCheckLimit Threshold (Maybe (Maybe Notifier))
  deriving (Eq, Show)

data NochangeTimingCheck = NochangeTimingCheck
  ReferenceEvent DataEvent StartEdgeOffset EndEdgeOffset (Maybe (Maybe Notifier))
  deriving (Eq, Show)

-- | A.7.5.2 System timing check command arguments
--

type TimecheckCondition = MintypmaxExpression

type ControlledReferenceEvent = ControlledTimingCheckEvent

type DataEvent = TimingCheckEvent

data DelayedData = DelayedData TerminalIdentifier (Maybe ConstantMintypmaxExpression)
  deriving (Eq, Show)

data DelayedReference = DelayedReference TerminalIdentifier (Maybe ConstantMintypmaxExpression)
  deriving (Eq, Show)

type EndEdgeOffset = MintypmaxExpression

type EventBasedFlag = ConstantExpression

type Notifier = VariableIdentifier

type ReferenceEvent = TimingCheckEvent

type RemainActiveFlag = ConstantMintypmaxExpression

type TimestampCondition = MintypmaxExpression

type StartEdgeOffset = MintypmaxExpression

type Threshold = ConstantExpression

type TimingCheckLimit = Expression

-- | A.7.5.3 System timing check event definitions
--

data TimingCheckEvent = TimingCheckEvent
  (Maybe TimingCheckEventControl) SpecifyTerminalDescriptor (Maybe TimingCheckCondition)
  deriving (Eq, Show)

data ControlledTimingCheckEvent = ControlledTimingCheckEvent
  TimingCheckEventControl SpecifyTerminalDescriptor (Maybe TimingCheckCondition)
  deriving (Eq, Show)

data TimingCheckEventControl
  = EdgeIdentifier_TimingCheckEventControl EdgeIdentifier
  | EdgeControlSpecifier_TimingCheckEventControl EdgeControlSpecifier
  deriving (Eq, Show)

type SpecifyTerminalDescriptor = Either SpecifyInputTerminalDescriptor SpecifyOutputTerminalDescriptor

data EdgeControlSpecifier = EdgeControlSpecifier [EdgeDescriptor]
  deriving (Eq, Show)

type EdgeDescriptor = Number

type ZeroOrOne = Number

type ZOrX = Number

type TimingCheckCondition = ScalarTimingCheckCondition

data ScalarTimingCheckCondition
  = ScalarTimingCheckCondition Expression
  | ScalarTimingCheckConditionNot Expression
  | ScalarTimingCheckConditionEquals Expression ScalarConstant
  | ScalarTimingCheckConditionEquivalent Expression ScalarConstant
  | ScalarTimingCheckConditionNotEquals Expression ScalarConstant
  | ScalarTimingCheckConditionNotEquivalent Expression ScalarConstant
  deriving (Eq, Show)

type ScalarConstant = Number


-- | A.8 Expressions
--
--   A.8.1 Concatenations
--

type Concatenation = [Expression]

type ConstantConcatenation = [ConstantExpression]

data ConstantMultipleConcatenation = ConstantMultipleConcatenation
  ConstantExpression ConstantConcatenation
  deriving (Eq, Show)

type ModulePathConcatenation = [ModulePathExpression]

data ModulePathMultipleConcatenation = ModulePathMultipleConcatenation
  ConstantExpression ModulePathConcatenation
  deriving (Eq, Show)

data MultipleConcatenation = MultipleConcatenation Expression Concatenation
  deriving (Eq, Show)

data StreamingConcatenation = StreamingConcatenation StreamOperator (Maybe SliceSize)
  StreamConcatenation
  deriving (Eq, Show)

data StreamOperator = Downstream | Upstream
  deriving (Eq, Show)

data SliceSize
  = SimpleType_SliceSize SimpleType
  | ConstantExpression_SliceSize ConstantExpression
  deriving (Eq, Show)

type StreamConcatenation = [StreamExpression]

data StreamExpression = StreamExpression Expression (Maybe ArrayRangeExpression)
  deriving (Eq, Show)

data ArrayRangeExpression
  = Expression_ArrayRangeExpression Expression
  | ArrayRangeZ Expression Expression
  | ArrayRangeP Expression Expression
  | ArrayRangeM Expression Expression
  deriving (Eq, Show)

data EmptyQueue = EmptyQueue
  deriving (Eq, Show)

-- | A.8.2 Subroutine calls
--

type ConstantFunctionCall = FunctionSubroutineCall

data TfCall = TfCall PsOrHierarchicalTfIdentifier [AttributeInstance] (Maybe ListOfArguments)
  deriving (Eq, Show)

data SystemTfCall
  = ListOfArguments_SystemTfCall SystemTfIdentifier (Maybe ListOfArguments)
  | DataType_SystemTfCall SystemTfIdentifier DataType (Maybe Expression)
  deriving (Eq, Show)

data SubroutineCall
  = TfCall_SubroutineCall TfCall
  | SystemTfCall_SubroutineCall SystemTfCall
  | MethodCall_SubroutineCall MethodCall
  | RandomizeCall_SubroutineCall (Maybe ()) RandomizeCall
  deriving (Eq, Show)

type FunctionSubroutineCall = SubroutineCall

data ListOfArguments = ListOfArguments (Maybe [Maybe Expression]) [(Identifier, Maybe Expression)]
  deriving (Eq, Show)

data MethodCall = MethodCall MethodCallRoot MethodCallBody
  deriving (Eq, Show)

data MethodCallBody
  = MethodCallBody MethodIdentifier [AttributeInstance] (Maybe ListOfArguments)
  | BuiltInMethodCall_MethodCallBody BuiltInMethodCall
  deriving (Eq, Show)

data BuiltInMethodCall
  = ArrayManipulationCall_BuiltInMethodCall ArrayManipulationCall
  | RandomizeCall_BuiltInMethodCall RandomizeCall
  deriving (Eq, Show)

data ArrayManipulationCall = ArrayManipulationCall
  ArrayMethodName [AttributeInstance]
  (Maybe ListOfArguments)
  (Maybe Expression)
  deriving (Eq, Show)

data RandomizeCall = RandomizeCall
  [AttributeInstance]
  (Maybe (Maybe (Either VariableIdentifierList ())))
  (Maybe (Maybe (Maybe IdentifierList), ConstraintBlock))
  deriving (Eq, Show)

type MethodCallRoot = Either Primary ImplicitClassHandle

data ArrayMethodName
  = MethodIdentifier_ArrayMethodName MethodIdentifier
  | UniqueAM | AndAM | OrAM | XorAM
  deriving (Eq, Show)


-- | A.8.3 Expressions
--

data IncOrDecExpression
  = PrefixIncOrDecExpression IncOrDecOperator [AttributeInstance] VariableLvalue
  | PostfixIncOrDecExpression VariableLvalue [AttributeInstance] IncOrDecOperator
  deriving (Eq, Show)

data ConditionalExpression = ConditionalExpression
  CondPredicate [AttributeInstance] Expression Expression
  deriving (Eq, Show)

data ConstantExpression
  = ConstantPrimary_ConstantExpression ConstantPrimary
  | UnaryConstantExpression UnaryOperator [AttributeInstance] ConstantPrimary
  | BinaryConstantExpression ConstantExpression BinaryOperator [AttributeInstance] ConstantExpression
  | TertiaryConstantExpression ConstantExpression
    [AttributeInstance] ConstantExpression
    ConstantExpression
  deriving (Eq, Show)

type ConstantMintypmaxExpression = Either ConstantExpression
  (ConstantExpression, ConstantExpression, ConstantExpression)

data ConstantParamExpression
  = ConstantMintypmaxExpression_ConstantParamExpression ConstantMintypmaxExpression
  | DataType_ConstantParamExpression DataType
  | DollarConstantParamExpression
  deriving (Eq, Show)

data ParamExpression
  = MintypmaxExpression_ParamExpression MintypmaxExpression
  | DataType_ParamExpression DataType
  | DollarParamExpression
  deriving (Eq, Show)

type ConstantRangeExpression = Either ConstantExpression ConstantPartSelectRange

type ConstantPartSelectRange = Either ConstantRange ConstantIndexedRange

type ConstantRange = (ConstantExpression, ConstantExpression)

data ConstantIndexedRange
  = PlusConstantIndexedRange ConstantExpression ConstantExpression
  | MinusConstantIndexedRange ConstantExpression ConstantExpression
  deriving (Eq, Show)

data Expression
  = Primary_Expression Primary
  | UnaryExpression UnaryOperator [AttributeInstance] Primary
  | IncOrDecExpression_Expression IncOrDecExpression
  | OperatorAssignment_Expression OperatorAssignment
  | BinaryExpression Expression BinaryOperator [AttributeInstance] Expression
  | ConditionalExpression_Expression ConditionalExpression
  | InsideExpression_Expression InsideExpression
  | TaggedUnionExpression_Expression TaggedUnionExpression
  deriving (Eq, Show)

data TaggedUnionExpression = TaggedUnionExpression MemberIdentifier (Maybe Expression)
  deriving (Eq, Show)

data InsideExpression = InsideExpression Expression OpenRangeList
  deriving (Eq, Show)

type ValueRange = Either Expression (Expression, Expression)

type MintypmaxExpression = Either Expression (Expression, Expression, Expression)

data ModulePathConditionalExpression = ModulePathConditionalExpression
  ModulePathExpression [AttributeInstance] ModulePathExpression ModulePathExpression
  deriving (Eq, Show)

data ModulePathExpression
  = ModulePathPrimary_ModulePathExpression ModulePathPrimary
  | UnaryModulePathExpression UnaryModulePathOperator [AttributeInstance] ModulePathPrimary
  | BinaryModulePathExpression ModulePathExpression BinaryModulePathOperator [AttributeInstance]
    ModulePathExpression
  | ModulePathConditionalExpression_ModulePathExpression ModulePathConditionalExpression
  deriving (Eq, Show)

type ModulePathMintypmaxExpression = Either ModulePathExpression
  (ModulePathExpression, ModulePathExpression, ModulePathExpression)

type PartSelectRange = Either ConstantRange IndexedRange

data IndexedRange
  = PlusIndexedRange Expression ConstantExpression
  | MinusIndexedRange Expression ConstantExpression
  deriving (Eq, Show)

type GenvarExpression = ConstantExpression

-- | A.8.4 Primaries
--

data ConstantPrimary
  = PrimaryLiteral_ConstantPrimary PrimaryLiteral
  | PsParameterIdentifier_ConstantPrimary PsParameterIdentifier ConstantSelect
  | SpecparamIdentifier_ConstantPrimary SpecparamIdentifier (Maybe ConstantRangeExpression)
  | GenvarIdentifier_ConstantPrimary GenvarIdentifier
  | FormalPortIdentifier_ConstantPrimary FormalPortIdentifier ConstantSelect
  | EnumIdentifier_ConstantPrimary (Maybe (Either PackageScope ClassScope)) EnumIdentifier
  | ConstantConcatenation_ConstantPrimary ConstantConcatenation (Maybe ConstantRangeExpression)
  | ConstantMultipleConcatenation_ConstantPrimary
    ConstantMultipleConcatenation (Maybe ConstantRangeExpression)
  | ConstantFunctionCall_ConstantPrimary ConstantFunctionCall
  | ConstantLetExpression_ConstantPrimary ConstantLetExpression
  | ConstantMintypmaxExpression_ConstantPrimary ConstantMintypmaxExpression
  | ConstantCast_ConstantPrimary ConstantCast
  | ConstantAssignmentPatternExpression_ConstantPrimary ConstantAssignmentPatternExpression
  | TypeReference_ConstantPrimary TypeReference
  deriving (Eq, Show)

data ModulePathPrimary
  = Number_ModulePathPrimary Number
  | Identifier_ModulePathPrimary Identifier
  | ModulePathConcatenation_ModulePathPrimary ModulePathConcatenation
  | ModulePathMultipleConcatenation_ModulePathPrimary ModulePathMultipleConcatenation
  | FunctionSubroutineCall_ModulePathPrimary FunctionSubroutineCall
  | ModulePathMintypmaxExpression_ModulePathPrimary ModulePathMintypmaxExpression
  deriving (Eq, Show)

data Primary
  = PrimaryLiteral_Primary PrimaryLiteral
  | HierarchicalIdentifier_Primary
    (Maybe (Either ClassQualifier PackageScope)) HierarchicalIdentifier Select
  | EmptyPrimary
  | Concatenation_Primary Concatenation (Maybe RangeExpression)
  | MultipleConcatenation_Primary MultipleConcatenation (Maybe RangeExpression)
  | FunctionSubroutineCall_Primary FunctionSubroutineCall
  | LetExpression_Primary LetExpression
  | MintypmaxExpression_Primary MintypmaxExpression
  | Cast_Primary Cast
  | AssignmentPatternExpression_Primary AssignmentPatternExpression
  | StreamingConcatenation_Primary StreamingConcatenation
  | SequenceMethodCall_Primary SequenceMethodCall
  | ThisPrimary
  | DollarPrimary
  | NullPrimary
  deriving (Eq, Show)

data ClassQualifier = ClassQualifier (Maybe ()) (Maybe (Either ImplicitClassHandle ClassScope))
  deriving (Eq, Show)

type RangeExpression = Either Expression PartSelectRange

data PrimaryLiteral
  = Number_PrimaryLiteral Number
  | TimeLiteral_PrimaryLiteral TimeLiteral
  | UnbasedUnsizedLiteral_PrimaryLiteral UnbasedUnsizedLiteral
  | StringLiteral_PrimaryLiteral StringLiteral
  deriving (Eq, Show)

data TimeLiteral
  = UnsignedTimeLiteral UnsignedNumber TimeUnit
  | FixedPointTimeLiteral FixedPointNumber TimeUnit
  deriving (Eq, Show)

type TimeUnit = Identifier

data ImplicitClassHandle = This | Super | ThisSuper
  deriving (Eq, Show)

type BitSelect = [Expression]

data Select = Select
  (Maybe ([(MemberIdentifier, BitSelect)], MemberIdentifier))
  BitSelect (Maybe PartSelectRange)
  deriving (Eq, Show)

data NonrangeSelect = NonrangeSelect
  (Maybe ([(MemberIdentifier, BitSelect)], MemberIdentifier))
  BitSelect
  deriving (Eq, Show)

type ConstantBitSelect = [ConstantExpression]

data ConstantSelect = ConstantSelect
  (Maybe ([(MemberIdentifier, ConstantBitSelect)], MemberIdentifier))
  ConstantBitSelect (Maybe ConstantPartSelectRange)
  deriving (Eq, Show)

data ConstantCast = ConstantCast CastingType ConstantExpression
  deriving (Eq, Show)

type ConstantLetExpression = LetExpression

data Cast = Cast CastingType Expression
  deriving (Eq, Show)


-- | A.8.5 Expression left-side values
--
data NetLvalue
  = PsOrHierarchicalNetIdentifier_NetLvalue PsOrHierarchicalNetIdentifier ConstantSelect
  | NetLvalues_NetLvalue [NetLvalue]
  | AssignmentPatternNetLvalue_NetLvalue
    (Maybe AssignmentPatternExpressionType) AssignmentPatternNetLvalue
  deriving (Eq, Show)

data VariableLvalue
  = HierarchicalVariableIdentifier_VariableLvalue HierarchicalVariableIdentifier Select
  | VariableLvalues_VariableLvalue [VariableLvalue]
  | AssignmentPatternVariableLvalue_VariableLvalue
    (Maybe AssignmentPatternExpressionType) AssignmentPatternVariableLvalue
  | StreamingConcatenation_VariableLvalue StreamingConcatenation
  deriving (Eq, Show)

data NonrangeVariableLvalue = NonrangeVariableLvalue (Maybe (Either ImplicitClassHandle PackageScope))
  HierarchicalVariableIdentifier NonrangeSelect
  deriving (Eq, Show)


-- | A.8.6 Operators
--

data UnaryOperator
  = PlusUn
  | MinusUn
  | TildeUn
  | NotUn
  | AmpUn
  | TildeAmpUn
  | PipeUn
  | TildePipeUn
  | CaretUn
  | TildeCaretUn
  | CaretTildeUn
  deriving (Eq, Show)


data BinaryOperator
  = PlusBin
  | MinusBin
  | StarBin
  | SlashBin
  | PercentBin
  | EqualsBin
  | NotEqualsBin
  | EquivalentBin
  | NotEquivalentBin
  | AndBin
  | OrBin
  | DoublestarBin
  | LtBin
  | LtEqBin
  | GtBin
  | GtEqBin
  | AmpBin
  | PipeBin
  | CaretBin
  | CaretTildeBin
  | TildeCaretBin
  | LtLtBin
  | GtGtBin
  | LtLtLtBin
  | GtGtGtBin
  | ArrowBin
  | IsoArrowBin
  deriving (Eq, Show)

data IncOrDecOperator = Increment | Decrement
  deriving (Eq, Show)

type UnaryModulePathOperator = UnaryOperator

type BinaryModulePathOperator = BinaryOperator


-- | A.8.7 Numbers
--
data Number
  = IntegralNumber_Number IntegralNumber
  | RealNumber_Number RealNumber
  deriving (Eq, Show)

data IntegralNumber
  = DecimalNumber_IntegralNumber DecimalNumber
  | OctalNumber_IntegralNumber OctalNumber
  | BinaryNumber_IntegralNumber BinaryNumber
  | HexNumber_IntegralNumber HexNumber
  deriving (Eq, Show)

data DecimalNumber
  = UnsignedNumber_DecimalNumber (Maybe Size) UnsignedNumber
  | X_DecimalNumber (Maybe Size) Text
  | Z_DecimalNumber (Maybe Size) Text 
  deriving (Eq, Show)

data BinaryNumber = BinaryNumber (Maybe Size) BinaryValue
  deriving (Eq, Show)

data OctalNumber = OctalNumber (Maybe Size) OctalValue
  deriving (Eq, Show)

data HexNumber = HexNumber (Maybe Size) HexValue
  deriving (Eq, Show)

data Sign = Plus | Minus
  deriving (Eq, Show)

type Size = UnsignedNumber

type UnsignedNumber = Text

data RealNumber
  = FixedPointNumber_RealNumber FixedPointNumber
  | UnsignedNumber_RealNumber UnsignedNumber (Maybe UnsignedNumber) (Maybe Sign) UnsignedNumber
  deriving (Eq, Show)

type FixedPointNumber = (UnsignedNumber, UnsignedNumber)

type BinaryValue = Text

type OctalValue = Text

type HexValue = Text

type DecimalBase = Text

type BinaryBase = Text

type OctalBase = Text

type HexBase = Text

data UnbasedUnsizedLiteral = UnbasedUnsizedLiteral UnsignedNumber
  deriving (Eq, Show)

-- | A.8.8 Strings
--
type StringLiteral = Text

-- | A.9 General
--
--   A.9.1 Attributes
--
type AttributeInstance = [AttrSpec]

data AttrSpec = AttrSpec AttrName (Maybe ConstantExpression)
  deriving (Eq, Show)

type AttrName = Identifier

-- | A.9.2 Comments
--


-- | A.9.3 Identifiers
--

type ArrayIdentifier = Identifier

type BlockIdentifier = Identifier

type BinIdentifier = Identifier

type CIdentifier = Text

type CellIdentifier = Identifier

type CheckerIdentifier = Identifier

type ClassIdentifier = Identifier

type ClassVariableIdentifier = VariableIdentifier

type ClockingIdentifier = Identifier

type ConfigIdentifier = Identifier

type ConstIdentifier = Identifier

type ConstraintIdentifier = Identifier

type CovergroupIdentifier = Identifier

type CovergroupVariableIdentifier = VariableIdentifier

type CoverPointIdentifier = Identifier

type CrossIdentifier = Identifier

type DynamicArrayVariableIdentifier = VariableIdentifier

type EnumIdentifier = Identifier

type FormalIdentifier = Identifier

type FormalPortIdentifier = Identifier

type FunctionIdentifier = Identifier

type GenerateBlockIdentifier = Identifier

type GenvarIdentifier = Identifier

type HierarchicalArrayIdentifier = HierarchicalIdentifier

type HierarchicalBlockIdentifier = HierarchicalIdentifier

type HierarchicalEventIdentifier = HierarchicalIdentifier

data HierarchicalIdentifier = HierarchicalIdentifier (Maybe ())
  [(Identifier, ConstantBitSelect)] Identifier
  deriving (Eq, Show)

type HierarchicalNetIdentifier = HierarchicalIdentifier

type HierarchicalParameterIdentifier = HierarchicalIdentifier

type HierarchicalPropertyIdentifier = HierarchicalIdentifier

type HierarchicalSequenceIdentifier = HierarchicalIdentifier

type HierarchicalTaskIdentifier = HierarchicalIdentifier

type HierarchicalTfIdentifier = HierarchicalIdentifier

type HierarchicalVariableIdentifier = HierarchicalIdentifier

type Identifier = Text

type IndexVariableIdentifier = Identifier

type InterfaceIdentifier = Identifier

type InterfaceInstanceIdentifier = Identifier

type InoutPortIdentifier = Identifier

type InputPortIdentifier = Identifier

type InstanceIdentifier = Identifier

type LibraryIdentifier = Identifier

type MemberIdentifier = Identifier

type MethodIdentifier = Identifier

type ModportIdentifier = Identifier

type ModuleIdentifier = Identifier

type NetIdentifier = Identifier

type NetTypeIdentifier = Identifier

type OutputPortIdentifier = Identifier

type PackageIdentifier = Identifier

type PackageScope = Maybe PackageIdentifier

type ParameterIdentifier = Identifier

type PortIdentifier = Identifier

type ProductionIdentifier = Identifier

type ProgramIdentifier = Identifier

type PropertyIdentifier = Identifier

data PsClassIdentifier = PsClassIdentifier (Maybe PackageScope) ClassIdentifier
  deriving (Eq, Show)

data PsCovergroupIdentifier = PsCovergroupIdentifier (Maybe PackageScope) CovergroupIdentifier
  deriving (Eq, Show)

data PsCheckerIdentifier = PsCheckerIdentifier (Maybe PackageScope) CheckerIdentifier
  deriving (Eq, Show)

data PsIdentifier = PsIdentifier (Maybe PackageScope) Identifier
  deriving (Eq, Show)

data PsOrHierarchicalArrayIdentifier = PsOrHierarchicalArrayIdentifier
  (Either ImplicitClassHandle (Either ClassScope PackageScope))
  HierarchicalArrayIdentifier
  deriving (Eq, Show)

data PsOrHierarchicalNetIdentifier
  = NetIdentifier_PsOrHierarchicalNetIdentifier (Maybe PackageScope) NetIdentifier
  | HierarchicalNetIdentifier_PsOrHierarchicalNetIdentifier HierarchicalNetIdentifier
  deriving (Eq, Show)

data PsOrHierarchicalPropertyIdentifier
  = PropertyIdentifier_PsOrHierarchicalPropertyIdentifier
    (Maybe PackageScope) PropertyIdentifier
  | HierarchicalPropertyIdentifier_PsOrHierarchicalPropertyIdentifier
    HierarchicalPropertyIdentifier
  deriving (Eq, Show)

data PsOrHierarchicalSequenceIdentifier
  = SequenceIdentifier_PsOrHierarchicalSequenceIdentifier
    (Maybe PackageScope) SequenceIdentifier
  | HierarchicalSequenceIdentifier_PsOrHierarchicalSequenceIdentifier
    HierarchicalSequenceIdentifier
  deriving (Eq, Show)

data PsOrHierarchicalTfIdentifier
  = TfIdentifier_PsOrHierarchicalTfIdentifier
    (Maybe PackageScope) TfIdentifier
  | HierarchicalTfIdentifier_PsOrHierarchicalTfIdentifier
    HierarchicalTfIdentifier
  deriving (Eq, Show)

data PsParameterIdentifier
  = PsParameterIdentifier
    (Maybe (Either PackageScope ClassScope))
    [(GenerateBlockIdentifier, Maybe ConstantExpression)]
    ParameterIdentifier
  deriving (Eq, Show)

data PsTypeIdentifier = PsTypeIdentifier (Maybe (Maybe PackageScope)) Identifier
  deriving (Eq, Show)

type SequenceIdentifier = Identifier

type SignalIdentifier = Identifier

type SimpleIdentifier = Text

type SpecparamIdentifier = Identifier

type SystemTfIdentifier = Text

type TaskIdentifier = Identifier

type TfIdentifier = Identifier

type TerminalIdentifier = Identifier

type TopmoduleIdentifier = Identifier

type TypeIdentifier = Identifier

type UdpIdentifier = Identifier

type VariableIdentifier = Identifier


type FilePathSpec = Identifier


