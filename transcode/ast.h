#include <optional>
#include <string>
#include <tuple>
#include <boost/variant.hpp>
#include <boost/mpl/vector.hpp>
#include <vector>

class ActionBlock;
class AlwaysConstruct;
enum class AlwaysKeyword ;
class AnonymousProgram;
class AnonymousProgramItem;
class AnsiPortDeclaration;
class ArrayManipulationCall;
class ArrayMethodName;
class ArrayPatternKey;
class ArrayRangeExpression;
class AssertPropertyStatement;
class AssertionItem;
class AssertionItemDeclaration;
class AssertionVariableDeclaration;
enum class AssignmentOperator ;
class AssignmentPattern;
class AssignmentPatternExpression;
class AssignmentPatternExpressionType;
class AssignmentPatternKey;
class AssignmentPatternNetLvalue;
class AssignmentPatternVariableLvalue;
class AssociativeDimension;
class AssumePropertyStatement;
class Ast;
class AttrName;
class AttrSpec;
class AttributeInstance;
class BinIdentifier;
typedef std::string BinaryBase;
enum class BinaryModulePathOperator ;
class BinaryNumber;
enum class BinaryOperator ;
typedef std::string BinaryValue;
class BindDirective;
class BindInstantiation;
class BindTargetInstance;
class BindTargetInstanceList;
class BindTargetScope;
class BinsExpression;
enum class BinsKeyword ;
class BinsOrEmpty;
class BinsOrOptions;
class BinsSelection;
class BinsSelectionOrOption;
class BitSelect;
class BlockEventExpression;
class BlockIdentifier;
class BlockItemDeclaration;
class BlockingAssignment;
class BooleanAbbrev;
class BuiltInMethodCall;
class CIdentifier;
class CaseExpression;
class CaseGenerateConstruct;
class CaseGenerateItem;
class CaseInsideItem;
class CaseItem;
class CaseItemExpression;
enum class CaseKeyword ;
class CasePatternItem;
class CaseStatement;
class Cast;
class CastingType;
class CellClause;
class CellIdentifier;
enum class ChargeStrength ;
class CheckerDeclaration;
class CheckerGenerateItem;
class CheckerIdentifier;
class CheckerInstantiation;
class CheckerOrGenerateItem;
class CheckerOrGenerateItemDeclaration;
enum class CheckerPortDirection ;
class CheckerPortItem;
class CheckerPortList;
class ClassConstraint;
class ClassConstructorDeclaration;
class ClassConstructorPrototype;
class ClassDeclaration;
class ClassIdentifier;
class ClassItem;
enum class ClassItemQualifier ;
class ClassMethod;
class ClassNew;
class ClassProperty;
class ClassQualifier;
class ClassScope;
class ClassType;
class ClassVariableIdentifier;
class ClockingDeclAssign;
class ClockingDeclaration;
class ClockingDirection;
class ClockingDrive;
class ClockingEvent;
class ClockingIdentifier;
class ClockingItem;
class ClockingSkew;
class Clockvar;
class ClockvarExpression;
class CmosSwitchInstance;
enum class CmosSwitchtype ;
class CombinationalBody;
class CombinationalEntry;
class Concatenation;
class ConcurrentAssertionItem;
class ConcurrentAssertionStatement;
class CondPattern;
class CondPredicate;
class ConditionalExpression;
class ConditionalGenerateConstruct;
class ConditionalStatement;
class ConfigDeclaration;
class ConfigIdentifier;
class ConfigRuleStatement;
class ConsecutiveRepetition;
class ConstIdentifier;
class ConstOrRangeExpression;
class ConstanLetExpression;
class ConstantAssignmentPatternExpression;
class ConstantBitSelect;
class ConstantCast;
class ConstantConcatenation;
class ConstantExpression;
class ConstantFunctionCall;
class ConstantIndexedRange;
class ConstantMintypmaxExpression;
class ConstantMultipleConcatenation;
class ConstantParamExpression;
class ConstantPartSelectRange;
class ConstantPrimary;
class ConstantRange;
class ConstantRangeExpression;
class ConstantSelect;
class ConstraintBlock;
class ConstraintBlockItem;
class ConstraintDeclaration;
class ConstraintExpression;
class ConstraintPrimary;
enum class ConstraintPrototypeQualifier ;
class ConstraintSet;
class ContinuousAssign;
class ContraintIdentifier;
class ContraintPrototype;
class ControlledReferenceEvent;
class ControlledTimingCheckEvent;
class CoverCross;
class CoverPoint;
class CoverPointIdentifier;
class CoverPropertyStatement;
class CoverSequenceStatement;
class CoverageEvent;
class CoverageOption;
class CoverageSpec;
class CoverageSpecOrOption;
class CovergroupDeclaration;
class CovergroupExpression;
class CovergroupIdentifier;
class CovergroupRangeList;
class CovergroupValueRange;
class CrossBody;
class CrossBodyItem;
class CrossIdentifier;
class CrossItem;
class CrossSetExpression;
class CurrentState;
class CycleDelay;
class CycleDelayConstRangeExpression;
class CycleDelayRange;
class DataDeclaration;
class DataEvent;
class DataSourceExpression;
class DataType;
class DataTypeOrImplicit;
class DataTypeOrVoid;
typedef std::string DecimalBase;
class DecimalNumber;
enum class DefaultClause;
class DefaultSkew;
class DeferredImmediateAssertStatement;
class DeferredImmediateAssertionItem;
class DeferredImmediateAssertionStatement;
class DeferredImmediateAssumeStatement;
class DeferredImmediateCoverStatement;
class DefparamAssignment;
class Delay2;
class Delay3;
class DelayControl;
class DelayOrEventControl;
class DelayValue;
class DelayedData;
class DelayedReference;
class Description;
class DesignStatement;
class DisableStatement;
class DistItem;
class DistList;
class DistWeight;
enum class DpiFunctionImportProperty ;
class DpiFunctionProto;
class DpiImportExport;
class DpiSpecString;
enum class DpiTaskImportProperty;
class DpiTaskProto;
class DriveStrength;
class DynamicArrayNew;
class DynamicArrayVariableIdentifier;
class EdgeControlSpecifier;
class EdgeDescriptor;
enum class EdgeIdentifier ;
class EdgeIndicator;
class EdgeInputList;
class EdgeSensitivePathDeclaration;
class EdgeSymbol;
class ElaborationSystemTask;
enum class EmptyQueue;
class EnableGateInstance;
enum class EnableGatetype ;
class EnableTerminal;
class EndEdgeOffset;
class EnumBaseType;
class EnumIdentifier;
class EnumNameDeclaration;
class ErrorLimitValue;
class EventBasedFlag;
class EventControl;
class EventExpression;
class EventTrigger;
class ExpectPropertyStatement;
class Expression;
class ExpressionOrCondPattern;
class ExpressionOrDist;
class ExternConstraintDeclaration;
class ExternTfDeclaration;
class FilePathSpec;
class FinalConstruct;
class FinishNumber;
class FixedPointNumber;
class ForInitialization;
class ForStep;
class ForStepAssignment;
class ForVariableDeclaration;
class FormalPortIdentifier;
class FullEdgeSensitivePathDescription;
class FullPathDescription;
class FullskewTimingCheck;
class FunctionBodyDeclaration;
class FunctionDataTypeOrImplicit;
class FunctionDeclaration;
class FunctionIdentifier;
class FunctionPrototype;
class FunctionStatement;
class FunctionStatementOrNull;
class FunctionSubroutineCall;
class GateInstantiation;
class GenerateBlock;
class GenerateBlockIdentifier;
class GenerateItem;
class GenerateRegion;
class GenvarDeclaration;
class GenvarExpression;
class GenvarIdentifier;
class GenvarInitialization;
class GenvarIteration;
class GotoRepetition;
typedef std::string HexBase;
class HexNumber;
typedef std::string HexValue;
class HierarchicalArrayIdentifier;
class HierarchicalBlockIdentifier;
class HierarchicalBtfIdentifier;
class HierarchicalEventIdentifier;
class HierarchicalIdentifier;
class HierarchicalInstance;
class HierarchicalNetIdentifier;
class HierarchicalParameterIdentifier;
class HierarchicalPropertyIdentifier;
class HierarchicalSequenceIdentifier;
class HierarchicalTaskIdentifier;
class HierarchicalTfIdentifier;
class HierarchicalVariableIdentifier;
class HoldTimingCheck;
typedef std::string Identifier;
class IdentifierList;
class IfGenerateConstruct;
class ImmediateAssertionStatement;
enum class ImplicitClassHandle ;
class ImplicitDataType;
enum class ImportExport ;
class IncOrDecExpression;
enum class IncOrDecOperator ;
class IncludeStatement;
class IndexVariableIdentifier;
class IndexedRange;
class InitVal;
class InitialConstruct;
class InoutDeclaration;
class InoutPortIdentifier;
class InoutTerminal;
class InputDeclaration;
class InputIdentifier;
class InputPortIdentifier;
class InputTerminal;
class InsideExpression;
class InstClause;
class InstName;
class InstanceIdentifier;
enum class IntegerAtomType ;
class IntegerCovergroupExpression;
class IntegerType;
enum class IntegerVectorType ;
class IntegralNumber;
class InterfaceAnsiHeader;
class InterfaceClassType;
class InterfaceDeclaration;
class InterfaceIdentifier;
class InterfaceInstantiation;
class InterfaceIntanceIdentifier;
class InterfaceItem;
class InterfaceNonAnsiHeader;
class InterfaceOrGenerateItem;
class InterfacePortDeclaration;
class InterfacePortHeader;
enum class JoinKeyword ;
class JumpStatement;
class LetActualArg;
class LetDeclaration;
class LetExpression;
class LetFormalType;
class LetIdentifier;
class LetListOfArguments;
class LetPortItem;
class LetPortList;
class LevelInputList;
class LevelSymbol;
class LiblistClause;
class LibraryDeclaration;
class LibraryDescription;
class LibraryIdentifier;
class LibraryText;
enum class Lifetime ;
class LimitValue;
class ListOfArguments;
class ListOfCheckerPortConnections;
class ListOfClockingDeclAssign;
class ListOfCrossItems;
class ListOfDefparamAssignments;
class ListOfGenvarIdentifiers;
class ListOfInterfaceIdentifiers;
class ListOfNetAssignments;
class ListOfNetDeclAssignments;
class ListOfParamAssignments;
class ListOfParameterAssignments;
class ListOfPathDelayExpressions;
class ListOfPathInputs;
class ListOfPathOutputs;
class ListOfPortConnections;
class ListOfPortDeclarations;
class ListOfPortIdentifiers;
class ListOfPorts;
class ListOfSpecparamAssignments;
class ListOfTfVariableIdentifiers;
class ListOfTypeAssignments;
class ListOfUdpPortIdentifiers;
class ListOfVariableAssignments;
class ListOfVariableDeclAssignments;
class ListOfVariableIdentifiers;
class LocalParameterDeclaration;
class LoopGenerateConstruct;
class LoopStatement;
class LoopVariables;
class MemberIdentifier;
class MethodCall;
class MethodCallBody;
class MethodCallRoot;
class MethodIdentifier;
class MethodPrototype;
class MethodQualifier;
class MintypmaxExpression;
class ModportClockingDeclaration;
class ModportDeclaration;
class ModportIdentifier;
class ModportItem;
class ModportPortsDeclaration;
class ModportSimplePort;
class ModportSimplePortsDeclaration;
class ModportTfPort;
class ModportTfPortsDeclaration;
class ModuleAnsiHeader;
class ModuleCommonItem;
class ModuleDeclaration;
class ModuleIdentifier;
class ModuleInstantiation;
class ModuleItem;
enum class ModuleKeyword ;
class ModuleNonAnsiHeader;
class ModuleOrGenerateItem;
class ModuleOrGenerateItemDeclaration;
class ModulePathConcatenation;
class ModulePathConditionalExpression;
class ModulePathExpression;
class ModulePathMintypmaxExpression;
class ModulePathMultipleConcatenation;
class ModulePathPrimary;
class MosSwitchInstance;
enum class MosSwitchtype ;
class MultipleConcatenation;
class NControlTerminal;
class NInputGateInstance;
enum class NInputGatetype ;
class NOutputGateInstance;
enum class NOutputGatetype ;
class NameOfInstance;
class NamedCheckerPortConnection;
class NamedParameterAssignment;
class NamedPortConnection;
class NetAlias;
class NetAssignment;
class NetDeclAssignment;
class NetDeclaration;
class NetIdentifier;
class NetLvalue;
class NetPortHeader;
class NetPortType;
enum class NetType ;
class NetTypeDeclaration;
class NetTypeIdentifier;
class NextState;
class NochangeTimingCheck;
class NonConsecutiveRepetition;
enum class NonIntegerType ;
class NonPortInterfaceItem;
class NonPortModuleItem;
class NonPortProgramItem;
class NonblockingAssignment;
class NonrangeSelect;
class NonrangeVariableLvalue;
class Notifier;
class Number;
typedef std::string OctalBase;
class OctalNumber;
typedef std::string OctalValue;
class OpenRangeList;
class OpenValueRange;
class OperatorAssignment;
class OrderedCheckerPortConnection;
class OrderedParameterAssignment;
class OrderedPortConnection;
class OutputDeclaration;
class OutputIdentifier;
class OutputPortIdentifier;
class OutputSymbol;
class OutputTerminal;
class OverloadDeclaration;
enum class OverloadOperator ;
class OverloadProtoFormals;
class PControlTerminal;
class PackageDeclaration;
class PackageExportDeclaration;
class PackageIdentifier;
class PackageImportDeclaration;
class PackageImportItem;
class PackageItem;
class PackageOrGenerateItemDeclaration;
class PackageScope;
class PackedDimension;
class ParBlock;
class ParallelEdgeSensitivePathDescription;
class ParallelPathDescription;
class ParamAssignment;
class ParamExpression;
class ParameterDeclaration;
class ParameterIdentifier;
class ParameterOverride;
class ParameterPortDeclaration;
class ParameterPortList;
class ParameterValueAssignment;
class PartSelectRange;
enum class PassEnSwitchType ;
class PassEnableSwitchInstance;
class PassSwitchInstance;
enum class PassSwitchtype ;
class PathDeclaration;
class PathDelayExpression;
class PathDelayValue;
class Pattern;
class PeriodTimingCheck;
enum class PolarityOperator ;
class Port;
class PortDeclaration;
enum class PortDirection ;
class PortExpression;
class PortIdentifier;
class PortReference;
class Primary;
class PrimaryLiteral;
class ProceduralAssertionStatement;
class ProceduralContinuousAssignment;
class ProceduralTimingControl;
class ProceduralTimingControlStatement;
class Production;
class ProductionIdentifier;
class ProductionItem;
class ProgramAnsiHeader;
class ProgramDeclaration;
class ProgramGenerateItem;
class ProgramIdentifier;
class ProgramInstantiation;
class ProgramItem;
class ProgramNonAnsiHeader;
class PropertyActualArg;
class PropertyCaseItem;
class PropertyDeclaration;
class PropertyExpr;
class PropertyFormalType;
class PropertyIdentifier;
class PropertyInstance;
class PropertyListOfArguments;
enum class PropertyLvarPortDirection;
class PropertyPortItem;
class PropertyPortList;
class PropertyQualifier;
class PropertySpec;
class PsCheckerIdentifier;
class PsClassIdentifier;
class PsCovergroupIdentifier;
class PsIdentifier;
class PsOrHierarchicalArrayIdentifier;
class PsOrHierarchicalNetIdentifier;
class PsOrHierarchicalPropertyIdentifier;
class PsOrHierarchicalSequenceIdentifier;
class PsOrHierarchicalTfIdentifier;
class PsParameterIdentifier;
class PsTypeIdentifier;
class PullGateInstance;
class PulldownStrength;
class PullupStrength;
class PulseControlSpecparam;
class PulsestyleDeclaration;
class QueueDimension;
class RandcaseItem;
class RandcaseStatement;
enum class RandomQualifier ;
class RandomizeCall;
class RandsequenceStatement;
class RangeExpression;
class RealNumber;
class RecoveryTimingCheck;
class RecremTimingCheck;
class RefDeclaration;
class ReferenceEvent;
class RejectLimitValue;
class RemainActiveFlag;
class RemovalTimingCheck;
class RepeatRange;
class RestrictPropertyStatement;
class RsCase;
class RsCaseItem;
class RsCodeBlock;
class RsIfElse;
class RsProd;
class RsProductionList;
class RsRepeat;
class RsRule;
class ScalarConstant;
class ScalarTimingCheckCondition;
class Select;
class SelectCondition;
class SelectExpression;
class SeqBlock;
class SeqInputList;
class SequenceAbbrev;
class SequenceActualArg;
class SequenceDeclaration;
class SequenceExpr;
class SequenceFormalType;
class SequenceIdentifier;
class SequenceInstance;
class SequenceListOfArguments;
enum class SequenceLvarPortDirection ;
class SequenceMatchItem;
class SequenceMethodCall;
class SequencePortItem;
class SequencePortList;
class SequentialBody;
class SequentialEntry;
class SetCovergroupExpression;
class SetupTimingCheck;
class SetupholdTimingCheck;
class ShowcancelledDeclaration;
enum class Sign ;
class SignalIdentifier;
enum class Signing ;
class SimpleImmediateAssertStatement;
class SimpleImmediateAssertionStatement;
class SimpleImmediateAssumeStatement;
class SimpleImmediateCoverStatement;
class SimplePathDeclaration;
class SimpleType;
class Size;
class SkewTimingCheck;
class SliceSize;
class SolveBeforeList;
class SourceText;
class SpecifyBlock;
class SpecifyInputTerminalDescriptor;
class SpecifyItem;
class SpecifyOutputTerminalDescriptor;
class SpecifyTerminalDescriptor;
class SpecparamAssignment;
class SpecparamDeclaration;
class SpecparamIdentifier;
class StartEdgeOffset;
class StateDependentPathDeclaration;
class Statement;
class StatementItem;
class StatementOrNull;
class StreamConcatenation;
class StreamExpression;
enum class StreamOperator ;
class StreamingConcatenation;
enum class Strength0 ;
enum class Strength1 ;
typedef std::string StringLiteral;
enum class StructUnion ;
class StructUnionMember;
class StructurePatternKey;
class SubroutineCall;
class SubroutineCallStatement;
class SystemTfCall;
typedef std::string SystemTfIdentifier;
class SystemTimingCheck;
class T01PathDelayExpression;
class T0xPathDelayExpression;
class T0zPathDelayExpression;
class T10PathDelayExpression;
class T1xPathDelayExpression;
class T1zPathDelayExpression;
class TPathDelayExpression;
class TaggedUnionExpression;
class TaskBodyDeclaration;
class TaskDeclaration;
class TaskIdentifier;
class TaskPrototype;
class TerminalIdentifier;
class TfCall;
class TfIdentifier;
class TfItemDeclaration;
class TfPortDeclaration;
class TfPortDirection;
class TfPortItem;
class TfPortList;
class TfallPathDelayExpression;
class Threshold;
class TimeLiteral;
class TimeUnit;
class TimecheckCondition;
class TimeskewTimingCheck;
class TimestampCondition;
class TimeunitsDeclaration;
class TimingCheckCondition;
class TimingCheckEvent;
class TimingCheckEventControl;
class TimingCheckLimit;
class TopmoduleIdentifier;
class TransItem;
class TransList;
class TransRangeList;
class TransSet;
class TrisePathDelayExpression;
class Tx0PathDelayExpression;
class Tx1PathDelayExpression;
class TxzPathDelayExpression;
class TypeAssignment;
class TypeDeclaration;
class TypeIdentifier;
class TypeReference;
class Tz0PathDelayExpression;
class Tz1PathDelayExpression;
class TzPathDelayExpression;
class TzxPathDelayExpression;
class UdpAnsiDeclaration;
class UdpBody;
class UdpDeclaration;
class UdpDeclarationPortList;
class UdpIdentifier;
class UdpInitialStatement;
class UdpInputDeclaration;
class UdpInstance;
class UdpInstantiation;
class UdpNonansiDeclaration;
class UdpOutputDeclaration;
class UdpPortDeclaration;
class UdpPortList;
class UdpRegDeclaration;
enum class UnaryModulePathOperator ;
enum class UnaryOperator ;
class UnbasedUnsizedLiteral;
enum class UniquePriority ;
class UniquenessConstraint;
class UnpackedDimension;
typedef std::string UnsignedNumber;
enum class UnsizedDimension;
class UseClause;
class ValueRange;
class VarDataType;
class VariableAssignment;
class VariableDeclAssignment;
class VariableDimension;
class VariableIdentifier;
class VariableIdentifierList;
class VariableLvalue;
class VariablePortHeader;
class VariablePortType;
class WaitStatement;
class WeightSpecification;
class WidthTimingCheck;
class WithCovergroupExpression;

class ActionBlock
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<StatementOrNull>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<Statement>, StatementOrNull>>>::type v2;
public:
	ActionBlock() { }
	boost::make_variant_over<v2>::type choice;
};

class AlwaysConstruct
{
public:
	AlwaysConstruct() { }
	AlwaysConstruct(AlwaysKeyword * _alwaysKeyword, Statement * _statement) { alwaysKeyword = _alwaysKeyword; statement = _statement; }

	AlwaysKeyword *alwaysKeyword;
	Statement *statement;
};

enum class AlwaysKeyword
{
	Always, Alwayscomb, Alwayslatch, Alwaysff
};

class AnonymousProgram
{
public:
	AnonymousProgram() { }
	AnonymousProgram(std::vector<AnonymousProgramItem> * _anonymousProgramItem) { anonymousProgramItem = _anonymousProgramItem; }

	std::vector<AnonymousProgramItem> *anonymousProgramItem;
};

class AnonymousProgramItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ClassConstructorDeclaration>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<CovergroupDeclaration>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<ClassDeclaration>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<FunctionDeclaration>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<TaskDeclaration>>::type v5;
public:
	AnonymousProgramItem() { }
	boost::make_variant_over<v5>::type choice;
};

class AnsiPortDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<PortDirection>, PortIdentifier, std::optional<Expression>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<VariablePortHeader>, PortIdentifier, std::vector<VariableDimension>, std::optional<ConstantExpression>>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::optional<InterfacePortHeader>, PortIdentifier, std::vector<UnpackedDimension>, std::optional<ConstantExpression>>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<std::optional<NetPortHeader>, PortIdentifier, std::vector<UnpackedDimension>, std::optional<ConstantExpression>>>>::type v4;
public:
	AnsiPortDeclaration() { }
	boost::make_variant_over<v4>::type choice;
};

class ArrayManipulationCall
{
public:
	ArrayManipulationCall() { }
	ArrayManipulationCall(ArrayMethodName * _arrayMethodName, std::vector<AttributeInstance> * _attributeInstance, std::optional<ListOfArguments> * _listOfArguments, std::optional<Expression> * _expression) { arrayMethodName = _arrayMethodName; attributeInstance = _attributeInstance; listOfArguments = _listOfArguments; expression = _expression; }

	ArrayMethodName *arrayMethodName;
	std::vector<AttributeInstance> *attributeInstance;
	std::optional<ListOfArguments> *listOfArguments;
	std::optional<Expression> *expression;
};

class ArrayMethodName
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<MethodIdentifier>>::type v1;
public:
	ArrayMethodName() { }
	boost::make_variant_over<v1>::type choice;
};

class ArrayPatternKey
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<AssignmentPatternKey>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ConstantExpression>>::type v2;
public:
	ArrayPatternKey() { }
	boost::make_variant_over<v2>::type choice;
};

class ArrayRangeExpression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<Expression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<Expression, Expression>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<Expression, Expression>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<Expression, Expression>>>::type v4;
public:
	ArrayRangeExpression() { }
	boost::make_variant_over<v4>::type choice;
};

class AssertPropertyStatement
{
public:
	AssertPropertyStatement() { }
	AssertPropertyStatement(PropertySpec * _propertySpec, ActionBlock * _actionBlock) { propertySpec = _propertySpec; actionBlock = _actionBlock; }

	PropertySpec *propertySpec;
	ActionBlock *actionBlock;
};

class AssertionItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<DeferredImmediateAssertionItem>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ConcurrentAssertionItem>>::type v2;
public:
	AssertionItem() { }
	boost::make_variant_over<v2>::type choice;
};

class AssertionItemDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<LetDeclaration>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<SequenceDeclaration>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<PropertyDeclaration>>::type v3;
public:
	AssertionItemDeclaration() { }
	boost::make_variant_over<v3>::type choice;
};

class AssertionVariableDeclaration
{
public:
	AssertionVariableDeclaration() { }
	AssertionVariableDeclaration(VarDataType * _varDataType, ListOfVariableDeclAssignments * _listOfVariableDeclAssignments) { varDataType = _varDataType; listOfVariableDeclAssignments = _listOfVariableDeclAssignments; }

	VarDataType *varDataType;
	ListOfVariableDeclAssignments *listOfVariableDeclAssignments;
};

enum class AssignmentOperator
{
	Assignop, Assplus, Assminus, Assstar, Assslash, Asspercent, Amp, Asspipe, Asscaret, Assshiftl, Assshiftr, Assshiftll, Assshiftrr
};

class AssignmentPattern
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<ConstantExpression, std::vector<Expression>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::vector<std::tuple<ArrayPatternKey, Expression>>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::vector<std::tuple<StructurePatternKey, Expression>>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::vector<Expression>>>::type v4;
public:
	AssignmentPattern() { }
	boost::make_variant_over<v4>::type choice;
};

class AssignmentPatternExpression
{
public:
	AssignmentPatternExpression() { }
	AssignmentPatternExpression(std::optional<AssignmentPatternExpressionType> * _assignmentPatternExpressionType, AssignmentPattern * _assignmentPattern) { assignmentPatternExpressionType = _assignmentPatternExpressionType; assignmentPattern = _assignmentPattern; }

	std::optional<AssignmentPatternExpressionType> *assignmentPatternExpressionType;
	AssignmentPattern *assignmentPattern;
};

class AssignmentPatternExpressionType
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<TypeReference>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<IntegerAtomType>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<PsParameterIdentifier>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<PsTypeIdentifier>>::type v4;
public:
	AssignmentPatternExpressionType() { }
	boost::make_variant_over<v4>::type choice;
};

class AssignmentPatternKey
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<SimpleType>>::type v1;
public:
	AssignmentPatternKey() { }
	boost::make_variant_over<v1>::type choice;
};

class AssignmentPatternNetLvalue
{
public:
	AssignmentPatternNetLvalue() { }
	AssignmentPatternNetLvalue(std::vector<NetLvalue> * _netLvalue) { netLvalue = _netLvalue; }

	std::vector<NetLvalue> *netLvalue;
};

class AssignmentPatternVariableLvalue
{
public:
	AssignmentPatternVariableLvalue() { }
	AssignmentPatternVariableLvalue(std::vector<VariableLvalue> * _variableLvalue) { variableLvalue = _variableLvalue; }

	std::vector<VariableLvalue> *variableLvalue;
};

class AssociativeDimension
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<DataType>>::type v1;
public:
	AssociativeDimension() { }
	boost::make_variant_over<v1>::type choice;
};

class AssumePropertyStatement
{
public:
	AssumePropertyStatement() { }
	AssumePropertyStatement(PropertySpec * _propertySpec, ActionBlock * _actionBlock) { propertySpec = _propertySpec; actionBlock = _actionBlock; }

	PropertySpec *propertySpec;
	ActionBlock *actionBlock;
};

class Ast
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<SourceText>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<LibraryText>>::type v2;
public:
	Ast() { }
	boost::make_variant_over<v2>::type choice;
};

class AttrName
{
public:
	AttrName() { }
	AttrName(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class AttrSpec
{
public:
	AttrSpec() { }
	AttrSpec(AttrName * _attrName, std::optional<ConstantExpression> * _constantExpression) { attrName = _attrName; constantExpression = _constantExpression; }

	AttrName *attrName;
	std::optional<ConstantExpression> *constantExpression;
};

class AttributeInstance
{
public:
	AttributeInstance() { }
	AttributeInstance(std::vector<AttrSpec> * _attrSpec) { attrSpec = _attrSpec; }

	std::vector<AttrSpec> *attrSpec;
};

class BinIdentifier
{
public:
	BinIdentifier() { }
	BinIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
typedef std::string BinaryBase;
enum class BinaryModulePathOperator
{
	Eq, Noteq, Andop, Orop, Amp, Pipe, Caret
};

class BinaryNumber
{
public:
	BinaryNumber() { }
	BinaryNumber(std::optional<Size> * _size, BinaryBase * _binaryBase, BinaryValue * _binaryValue) { size = _size; binaryBase = _binaryBase; binaryValue = _binaryValue; }

	std::optional<Size> *size;
	BinaryBase *binaryBase;
	BinaryValue *binaryValue;
};

enum class BinaryOperator
{
	Plus, Minus, Star, Slash, Percent, Eq, Noteq, Equivalent, Notequivalent, Andop, Orop, Amp, Pipe, Caret
};

typedef std::string BinaryValue;
class BindDirective
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<BindTargetInstance, BindInstantiation>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<BindTargetScope, std::optional<BindTargetInstanceList>, BindInstantiation>>>::type v2;
public:
	BindDirective() { }
	boost::make_variant_over<v2>::type choice;
};

class BindInstantiation
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<CheckerInstantiation>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<InterfaceInstantiation>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<ModuleInstantiation>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<ProgramInstantiation>>::type v4;
public:
	BindInstantiation() { }
	boost::make_variant_over<v4>::type choice;
};

class BindTargetInstance
{
public:
	BindTargetInstance() { }
	BindTargetInstance(HierarchicalIdentifier * _hierarchicalIdentifier, ConstantBitSelect * _constantBitSelect) { hierarchicalIdentifier = _hierarchicalIdentifier; constantBitSelect = _constantBitSelect; }

	HierarchicalIdentifier *hierarchicalIdentifier;
	ConstantBitSelect *constantBitSelect;
};

class BindTargetInstanceList
{
public:
	BindTargetInstanceList() { }
	BindTargetInstanceList(BindTargetInstance * _bindTargetInstance) { bindTargetInstance = _bindTargetInstance; }

	BindTargetInstance *bindTargetInstance;
};
class BindTargetScope
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<InterfaceIdentifier>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ModuleIdentifier>>::type v2;
public:
	BindTargetScope() { }
	boost::make_variant_over<v2>::type choice;
};

class BinsExpression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<CoverPointIdentifier, std::optional<BinIdentifier>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<VariableIdentifier>>::type v2;
public:
	BinsExpression() { }
	boost::make_variant_over<v2>::type choice;
};

enum class BinsKeyword
{
	Bins, Illegalbins, Ignorebins
};

class BinsOrEmpty
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, std::vector<BinsOrOptions>>>>::type v1;
public:
	BinsOrEmpty() { }
	boost::make_variant_over<v1>::type choice;
};

class BinsOrOptions
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<BinsKeyword, BinIdentifier, std::optional<Expression>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<BinsKeyword, BinIdentifier, std::optional<std::optional<CovergroupExpression>>, std::optional<Expression>>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<BinsKeyword, BinIdentifier, std::optional<int>, TransList, std::optional<Expression>>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<BinsKeyword, BinIdentifier, std::optional<std::optional<CovergroupExpression>>, SetCovergroupExpression, std::optional<Expression>>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<BinsKeyword, BinIdentifier, std::optional<std::optional<CovergroupExpression>>, CoverPointIdentifier, std::optional<WithCovergroupExpression>, std::optional<Expression>>>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<std::tuple<BinsKeyword, BinIdentifier, std::optional<std::optional<CovergroupExpression>>, CovergroupRangeList, std::optional<WithCovergroupExpression>, std::optional<Expression>>>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<CoverageOption>>::type v7;
public:
	BinsOrOptions() { }
	boost::make_variant_over<v7>::type choice;
};

class BinsSelection
{
public:
	BinsSelection() { }
	BinsSelection(BinsKeyword * _binsKeyword, BinIdentifier * _binIdentifier, SelectExpression * _selectExpression, std::optional<Expression> * _expression) { binsKeyword = _binsKeyword; binIdentifier = _binIdentifier; selectExpression = _selectExpression; expression = _expression; }

	BinsKeyword *binsKeyword;
	BinIdentifier *binIdentifier;
	SelectExpression *selectExpression;
	std::optional<Expression> *expression;
};

class BinsSelectionOrOption
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, BinsSelection>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, CoverageOption>>>::type v2;
public:
	BinsSelectionOrOption() { }
	boost::make_variant_over<v2>::type choice;
};

class BitSelect
{
public:
	BitSelect() { }
	BitSelect(Expression * _expression) { expression = _expression; }

	Expression *expression;
};
class BlockEventExpression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<HierarchicalBtfIdentifier>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<HierarchicalBtfIdentifier>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<BlockEventExpression, BlockEventExpression>>>::type v3;
public:
	BlockEventExpression() { }
	boost::make_variant_over<v3>::type choice;
};

class BlockIdentifier
{
public:
	BlockIdentifier() { }
	BlockIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class BlockItemDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, LetDeclaration>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, OverloadDeclaration>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ParameterDeclaration>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, LocalParameterDeclaration>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, DataDeclaration>>>::type v5;
public:
	BlockItemDeclaration() { }
	boost::make_variant_over<v5>::type choice;
};

class BlockingAssignment
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<OperatorAssignment>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<PackageScope, HierarchicalVariableIdentifier, Select, ClassNew>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<ClassScope, HierarchicalVariableIdentifier, Select, ClassNew>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<ImplicitClassHandle, HierarchicalVariableIdentifier, Select, ClassNew>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<NonrangeVariableLvalue, DynamicArrayNew>>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<std::tuple<VariableLvalue, DelayOrEventControl, Expression>>>::type v6;
public:
	BlockingAssignment() { }
	boost::make_variant_over<v6>::type choice;
};

class BooleanAbbrev
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<GotoRepetition>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<NonConsecutiveRepetition>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<ConsecutiveRepetition>>::type v3;
public:
	BooleanAbbrev() { }
	boost::make_variant_over<v3>::type choice;
};

class BuiltInMethodCall
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<RandomizeCall>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ArrayManipulationCall>>::type v2;
public:
	BuiltInMethodCall() { }
	boost::make_variant_over<v2>::type choice;
};

class CIdentifier
{
public:
	CIdentifier() { }
	CIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class CaseExpression
{
public:
	CaseExpression() { }
	CaseExpression(Expression * _expression) { expression = _expression; }

	Expression *expression;
};
class CaseGenerateConstruct
{
public:
	CaseGenerateConstruct() { }
	CaseGenerateConstruct(ConstantExpression * _constantExpression, std::vector<CaseGenerateItem> * _caseGenerateItem) { constantExpression = _constantExpression; caseGenerateItem = _caseGenerateItem; }

	ConstantExpression *constantExpression;
	std::vector<CaseGenerateItem> *caseGenerateItem;
};

class CaseGenerateItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<GenerateBlock>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<ConstantExpression>, GenerateBlock>>>::type v2;
public:
	CaseGenerateItem() { }
	boost::make_variant_over<v2>::type choice;
};

class CaseInsideItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<StatementOrNull>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<OpenRangeList, StatementOrNull>>>::type v2;
public:
	CaseInsideItem() { }
	boost::make_variant_over<v2>::type choice;
};

class CaseItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<StatementOrNull>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<CaseItemExpression>, StatementOrNull>>>::type v2;
public:
	CaseItem() { }
	boost::make_variant_over<v2>::type choice;
};

class CaseItemExpression
{
public:
	CaseItemExpression() { }
	CaseItemExpression(Expression * _expression) { expression = _expression; }

	Expression *expression;
};
enum class CaseKeyword
{
	Case, Casez, Casex
};

class CasePatternItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<StatementOrNull>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<Pattern, std::optional<Expression>, StatementOrNull>>>::type v2;
public:
	CasePatternItem() { }
	boost::make_variant_over<v2>::type choice;
};

class CaseStatement
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<UniquePriority>, CaseExpression, std::vector<CaseInsideItem>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<UniquePriority>, CaseKeyword, CaseExpression, std::vector<CasePatternItem>>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::optional<UniquePriority>, CaseKeyword, CaseExpression, std::vector<CaseItem>>>>::type v3;
public:
	CaseStatement() { }
	boost::make_variant_over<v3>::type choice;
};

class Cast
{
public:
	Cast() { }
	Cast(CastingType * _castingType, Expression * _expression) { castingType = _castingType; expression = _expression; }

	CastingType *castingType;
	Expression *expression;
};

class CastingType
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<Signing>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ConstantPrimary>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<SimpleType>>::type v3;
public:
	CastingType() { }
	boost::make_variant_over<v3>::type choice;
};

class CellClause
{
public:
	CellClause() { }
	CellClause(std::optional<LibraryIdentifier> * _libraryIdentifier, CellIdentifier * _cellIdentifier) { libraryIdentifier = _libraryIdentifier; cellIdentifier = _cellIdentifier; }

	std::optional<LibraryIdentifier> *libraryIdentifier;
	CellIdentifier *cellIdentifier;
};

class CellIdentifier
{
public:
	CellIdentifier() { }
	CellIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
enum class ChargeStrength
{
	Small, Medium, Large
};

class CheckerDeclaration
{
public:
	CheckerDeclaration() { }
	CheckerDeclaration(CheckerIdentifier * _checkerIdentifier0, std::optional<std::optional<CheckerPortList>> * _checkerPortList, std::vector<std::tuple<std::vector<AttributeInstance>, CheckerOrGenerateItem>> * _attributeInstance, std::optional<CheckerIdentifier> * _checkerIdentifier3) { checkerIdentifier0 = _checkerIdentifier0; checkerPortList = _checkerPortList; attributeInstance = _attributeInstance; checkerIdentifier3 = _checkerIdentifier3; }

	CheckerIdentifier *checkerIdentifier0;
	std::optional<std::optional<CheckerPortList>> *checkerPortList;
	std::vector<std::tuple<std::vector<AttributeInstance>, CheckerOrGenerateItem>> *attributeInstance;
	std::optional<CheckerIdentifier> *checkerIdentifier3;
};

class CheckerGenerateItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ElaborationSystemTask>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<GenerateRegion>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<ConditionalGenerateConstruct>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<LoopGenerateConstruct>>::type v4;
public:
	CheckerGenerateItem() { }
	boost::make_variant_over<v4>::type choice;
};

class CheckerIdentifier
{
public:
	CheckerIdentifier() { }
	CheckerIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class CheckerInstantiation
{
public:
	CheckerInstantiation() { }
	CheckerInstantiation(PsCheckerIdentifier * _psCheckerIdentifier, NameOfInstance * _nameOfInstance, std::optional<ListOfCheckerPortConnections> * _listOfCheckerPortConnections) { psCheckerIdentifier = _psCheckerIdentifier; nameOfInstance = _nameOfInstance; listOfCheckerPortConnections = _listOfCheckerPortConnections; }

	PsCheckerIdentifier *psCheckerIdentifier;
	NameOfInstance *nameOfInstance;
	std::optional<ListOfCheckerPortConnections> *listOfCheckerPortConnections;
};

class CheckerOrGenerateItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<CheckerGenerateItem>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ContinuousAssign>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<AssertionItem>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<FinalConstruct>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<AlwaysConstruct>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<InitialConstruct>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<CheckerOrGenerateItemDeclaration>>::type v7;
public:
	CheckerOrGenerateItem() { }
	boost::make_variant_over<v7>::type choice;
};

class CheckerOrGenerateItemDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ExpressionOrDist>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ClockingIdentifier>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<ClockingDeclaration>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<GenvarDeclaration>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<OverloadDeclaration>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<CovergroupDeclaration>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<AssertionItemDeclaration>>::type v7;
	typedef boost::mpl::push_front<v7, boost::recursive_wrapper<CheckerDeclaration>>::type v8;
	typedef boost::mpl::push_front<v8, boost::recursive_wrapper<FunctionDeclaration>>::type v9;
	typedef boost::mpl::push_front<v9, boost::recursive_wrapper<DataDeclaration>>::type v10;
public:
	CheckerOrGenerateItemDeclaration() { }
	boost::make_variant_over<v10>::type choice;
};

enum class CheckerPortDirection
{
	Input, Output
};

class CheckerPortItem
{
public:
	CheckerPortItem() { }
	CheckerPortItem(std::vector<AttributeInstance> * _attributeInstance, std::optional<CheckerPortDirection> * _checkerPortDirection, PropertyFormalType * _propertyFormalType, FormalPortIdentifier * _formalPortIdentifier, std::vector<VariableDimension> * _variableDimension, std::optional<PropertyActualArg> * _propertyActualArg) { attributeInstance = _attributeInstance; checkerPortDirection = _checkerPortDirection; propertyFormalType = _propertyFormalType; formalPortIdentifier = _formalPortIdentifier; variableDimension = _variableDimension; propertyActualArg = _propertyActualArg; }

	std::vector<AttributeInstance> *attributeInstance;
	std::optional<CheckerPortDirection> *checkerPortDirection;
	PropertyFormalType *propertyFormalType;
	FormalPortIdentifier *formalPortIdentifier;
	std::vector<VariableDimension> *variableDimension;
	std::optional<PropertyActualArg> *propertyActualArg;
};

class CheckerPortList
{
public:
	CheckerPortList() { }
	CheckerPortList(CheckerPortItem * _checkerPortItem) { checkerPortItem = _checkerPortItem; }

	CheckerPortItem *checkerPortItem;
};
class ClassConstraint
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ConstraintDeclaration>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ContraintPrototype>>::type v2;
public:
	ClassConstraint() { }
	boost::make_variant_over<v2>::type choice;
};

class ClassConstructorDeclaration
{
public:
	ClassConstructorDeclaration() { }
	ClassConstructorDeclaration(std::optional<ClassScope> * _classScope, std::optional<std::optional<TfPortList>> * _tfPortList, std::vector<BlockItemDeclaration> * _blockItemDeclaration, std::optional<std::optional<ListOfArguments>> * _listOfArguments, std::vector<FunctionStatementOrNull> * _functionStatementOrNull, std::optional<int> * _discard) { classScope = _classScope; tfPortList = _tfPortList; blockItemDeclaration = _blockItemDeclaration; listOfArguments = _listOfArguments; functionStatementOrNull = _functionStatementOrNull; discard = _discard; }

	std::optional<ClassScope> *classScope;
	std::optional<std::optional<TfPortList>> *tfPortList;
	std::vector<BlockItemDeclaration> *blockItemDeclaration;
	std::optional<std::optional<ListOfArguments>> *listOfArguments;
	std::vector<FunctionStatementOrNull> *functionStatementOrNull;
	std::optional<int> *discard;
};

class ClassConstructorPrototype
{
public:
	ClassConstructorPrototype() { }
	ClassConstructorPrototype(std::optional<std::optional<TfPortList>> * _tfPortList) { tfPortList = _tfPortList; }

	std::optional<std::optional<TfPortList>> *tfPortList;
};

class ClassDeclaration
{
public:
	ClassDeclaration() { }
	ClassDeclaration(std::optional<Lifetime> * _lifetime, ClassIdentifier * _classIdentifier1, std::optional<ParameterPortList> * _parameterPortList, std::optional<std::tuple<ClassType, std::optional<ListOfArguments>>> * _classType, std::optional<std::vector<InterfaceClassType>> * _interfaceClassType, std::vector<ClassItem> * _classItem, std::optional<ClassIdentifier> * _classIdentifier6) { lifetime = _lifetime; classIdentifier1 = _classIdentifier1; parameterPortList = _parameterPortList; classType = _classType; interfaceClassType = _interfaceClassType; classItem = _classItem; classIdentifier6 = _classIdentifier6; }

	std::optional<Lifetime> *lifetime;
	ClassIdentifier *classIdentifier1;
	std::optional<ParameterPortList> *parameterPortList;
	std::optional<std::tuple<ClassType, std::optional<ListOfArguments>>> *classType;
	std::optional<std::vector<InterfaceClassType>> *interfaceClassType;
	std::vector<ClassItem> *classItem;
	std::optional<ClassIdentifier> *classIdentifier6;
};

class ClassIdentifier
{
public:
	ClassIdentifier() { }
	ClassIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class ClassItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ParameterDeclaration>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<LocalParameterDeclaration>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, CovergroupDeclaration>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ClassDeclaration>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ClassConstraint>>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ClassMethod>>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ClassProperty>>>::type v7;
public:
	ClassItem() { }
	boost::make_variant_over<v7>::type choice;
};

enum class ClassItemQualifier
{
	Static, Protected, Local
};

class ClassMethod
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::vector<MethodQualifier>, ClassConstructorPrototype>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<MethodQualifier>, ClassConstructorDeclaration>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::vector<MethodQualifier>, MethodPrototype>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<std::vector<ClassItemQualifier>, MethodPrototype>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<std::vector<MethodQualifier>, FunctionDeclaration>>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<std::tuple<std::vector<MethodQualifier>, TaskDeclaration>>>::type v6;
public:
	ClassMethod() { }
	boost::make_variant_over<v6>::type choice;
};

class ClassNew
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<Expression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<ClassScope>, std::optional<ListOfArguments>>>>::type v2;
public:
	ClassNew() { }
	boost::make_variant_over<v2>::type choice;
};

class ClassProperty
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::vector<ClassItemQualifier>, DataType, ConstIdentifier, std::optional<ConstantExpression>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<PropertyQualifier>, DataDeclaration>>>::type v2;
public:
	ClassProperty() { }
	boost::make_variant_over<v2>::type choice;
};

class ClassQualifier
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<int>, std::optional<ClassScope>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<int>, std::optional<ImplicitClassHandle>>>>::type v2;
public:
	ClassQualifier() { }
	boost::make_variant_over<v2>::type choice;
};

class ClassScope
{
public:
	ClassScope() { }
	ClassScope(ClassType * _classType) { classType = _classType; }

	ClassType *classType;
};

class ClassType
{
public:
	ClassType() { }
	ClassType(PsClassIdentifier * _psClassIdentifier, std::optional<ParameterValueAssignment> * _parameterValueAssignment, std::vector<std::tuple<ClassIdentifier, std::optional<ParameterValueAssignment>>> * _classIdentifier) { psClassIdentifier = _psClassIdentifier; parameterValueAssignment = _parameterValueAssignment; classIdentifier = _classIdentifier; }

	PsClassIdentifier *psClassIdentifier;
	std::optional<ParameterValueAssignment> *parameterValueAssignment;
	std::vector<std::tuple<ClassIdentifier, std::optional<ParameterValueAssignment>>> *classIdentifier;
};

class ClassVariableIdentifier
{
public:
	ClassVariableIdentifier() { }
	ClassVariableIdentifier(VariableIdentifier * _variableIdentifier) { variableIdentifier = _variableIdentifier; }

	VariableIdentifier *variableIdentifier;
};
class ClockingDeclAssign
{
public:
	ClockingDeclAssign() { }
	ClockingDeclAssign(SignalIdentifier * _signalIdentifier, std::optional<Expression> * _expression) { signalIdentifier = _signalIdentifier; expression = _expression; }

	SignalIdentifier *signalIdentifier;
	std::optional<Expression> *expression;
};

class ClockingDeclaration
{
public:
	ClockingDeclaration() { }
	ClockingDeclaration(std::optional<ClockingIdentifier> * _clockingIdentifier0, ClockingEvent * _clockingEvent, std::vector<ClockingItem> * _clockingItem, std::optional<ClockingIdentifier> * _clockingIdentifier3) { clockingIdentifier0 = _clockingIdentifier0; clockingEvent = _clockingEvent; clockingItem = _clockingItem; clockingIdentifier3 = _clockingIdentifier3; }

	std::optional<ClockingIdentifier> *clockingIdentifier0;
	ClockingEvent *clockingEvent;
	std::vector<ClockingItem> *clockingItem;
	std::optional<ClockingIdentifier> *clockingIdentifier3;
};

class ClockingDirection
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<ClockingSkew>, std::optional<ClockingSkew>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::optional<ClockingSkew>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::optional<ClockingSkew>>>::type v3;
public:
	ClockingDirection() { }
	boost::make_variant_over<v3>::type choice;
};

class ClockingDrive
{
public:
	ClockingDrive() { }
	ClockingDrive(ClockvarExpression * _clockvarExpression, std::optional<CycleDelay> * _cycleDelay, Expression * _expression) { clockvarExpression = _clockvarExpression; cycleDelay = _cycleDelay; expression = _expression; }

	ClockvarExpression *clockvarExpression;
	std::optional<CycleDelay> *cycleDelay;
	Expression *expression;
};

class ClockingEvent
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<EventExpression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<Identifier>>::type v2;
public:
	ClockingEvent() { }
	boost::make_variant_over<v2>::type choice;
};

class ClockingIdentifier
{
public:
	ClockingIdentifier() { }
	ClockingIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class ClockingItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, AssertionItemDeclaration>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<ClockingDirection, ListOfClockingDeclAssign>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<DefaultSkew>>::type v3;
public:
	ClockingItem() { }
	boost::make_variant_over<v3>::type choice;
};

class ClockingSkew
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<DelayControl>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<EdgeIdentifier, std::optional<DelayControl>>>>::type v2;
public:
	ClockingSkew() { }
	boost::make_variant_over<v2>::type choice;
};

class Clockvar
{
public:
	Clockvar() { }
	Clockvar(HierarchicalIdentifier * _hierarchicalIdentifier) { hierarchicalIdentifier = _hierarchicalIdentifier; }

	HierarchicalIdentifier *hierarchicalIdentifier;
};
class ClockvarExpression
{
public:
	ClockvarExpression() { }
	ClockvarExpression(Clockvar * _clockvar, Select * _select) { clockvar = _clockvar; select = _select; }

	Clockvar *clockvar;
	Select *select;
};

class CmosSwitchInstance
{
public:
	CmosSwitchInstance() { }
	CmosSwitchInstance(std::optional<NameOfInstance> * _nameOfInstance, OutputTerminal * _outputTerminal, InputTerminal * _inputTerminal, NControlTerminal * _nControlTerminal, PControlTerminal * _pControlTerminal) { nameOfInstance = _nameOfInstance; outputTerminal = _outputTerminal; inputTerminal = _inputTerminal; nControlTerminal = _nControlTerminal; pControlTerminal = _pControlTerminal; }

	std::optional<NameOfInstance> *nameOfInstance;
	OutputTerminal *outputTerminal;
	InputTerminal *inputTerminal;
	NControlTerminal *nControlTerminal;
	PControlTerminal *pControlTerminal;
};

enum class CmosSwitchtype
{
	Cmos, Rcmos
};

class CombinationalBody
{
public:
	CombinationalBody() { }
	CombinationalBody(std::vector<CombinationalEntry> * _combinationalEntry) { combinationalEntry = _combinationalEntry; }

	std::vector<CombinationalEntry> *combinationalEntry;
};

class CombinationalEntry
{
public:
	CombinationalEntry() { }
	CombinationalEntry(LevelInputList * _levelInputList, OutputSymbol * _outputSymbol) { levelInputList = _levelInputList; outputSymbol = _outputSymbol; }

	LevelInputList *levelInputList;
	OutputSymbol *outputSymbol;
};

class Concatenation
{
public:
	Concatenation() { }
	Concatenation(std::vector<Expression> * _expression) { expression = _expression; }

	std::vector<Expression> *expression;
};

class ConcurrentAssertionItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<CheckerInstantiation>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<BlockIdentifier>, ConcurrentAssertionStatement>>>::type v2;
public:
	ConcurrentAssertionItem() { }
	boost::make_variant_over<v2>::type choice;
};

class ConcurrentAssertionStatement
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<RestrictPropertyStatement>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<CoverSequenceStatement>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<CoverPropertyStatement>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<AssumePropertyStatement>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<AssertPropertyStatement>>::type v5;
public:
	ConcurrentAssertionStatement() { }
	boost::make_variant_over<v5>::type choice;
};

class CondPattern
{
public:
	CondPattern() { }
	CondPattern(Expression * _expression, Pattern * _pattern) { expression = _expression; pattern = _pattern; }

	Expression *expression;
	Pattern *pattern;
};

class CondPredicate
{
public:
	CondPredicate() { }
	CondPredicate(ExpressionOrCondPattern * _expressionOrCondPattern) { expressionOrCondPattern = _expressionOrCondPattern; }

	ExpressionOrCondPattern *expressionOrCondPattern;
};
class ConditionalExpression
{
public:
	ConditionalExpression() { }
	ConditionalExpression(CondPredicate * _condPredicate, std::vector<AttributeInstance> * _attributeInstance, Expression * _expression2, Expression * _expression3) { condPredicate = _condPredicate; attributeInstance = _attributeInstance; expression2 = _expression2; expression3 = _expression3; }

	CondPredicate *condPredicate;
	std::vector<AttributeInstance> *attributeInstance;
	Expression *expression2;
	Expression *expression3;
};

class ConditionalGenerateConstruct
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<CaseGenerateConstruct>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<IfGenerateConstruct>>::type v2;
public:
	ConditionalGenerateConstruct() { }
	boost::make_variant_over<v2>::type choice;
};

class ConditionalStatement
{
public:
	ConditionalStatement() { }
	ConditionalStatement(std::optional<UniquePriority> * _uniquePriority, CondPredicate * _condPredicate1, StatementOrNull * _statementOrNull2, std::vector<std::tuple<CondPredicate, StatementOrNull>> * _condPredicate3, std::optional<StatementOrNull> * _statementOrNull4) { uniquePriority = _uniquePriority; condPredicate1 = _condPredicate1; statementOrNull2 = _statementOrNull2; condPredicate3 = _condPredicate3; statementOrNull4 = _statementOrNull4; }

	std::optional<UniquePriority> *uniquePriority;
	CondPredicate *condPredicate1;
	StatementOrNull *statementOrNull2;
	std::vector<std::tuple<CondPredicate, StatementOrNull>> *condPredicate3;
	std::optional<StatementOrNull> *statementOrNull4;
};

class ConfigDeclaration
{
public:
	ConfigDeclaration() { }
	ConfigDeclaration(ConfigIdentifier * _configIdentifier0, std::vector<LocalParameterDeclaration> * _localParameterDeclaration, DesignStatement * _designStatement, std::vector<ConfigRuleStatement> * _configRuleStatement, std::optional<ConfigIdentifier> * _configIdentifier4) { configIdentifier0 = _configIdentifier0; localParameterDeclaration = _localParameterDeclaration; designStatement = _designStatement; configRuleStatement = _configRuleStatement; configIdentifier4 = _configIdentifier4; }

	ConfigIdentifier *configIdentifier0;
	std::vector<LocalParameterDeclaration> *localParameterDeclaration;
	DesignStatement *designStatement;
	std::vector<ConfigRuleStatement> *configRuleStatement;
	std::optional<ConfigIdentifier> *configIdentifier4;
};

class ConfigIdentifier
{
public:
	ConfigIdentifier() { }
	ConfigIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class ConfigRuleStatement
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<CellClause, UseClause>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<CellClause, LiblistClause>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<InstClause, UseClause>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<InstClause, LiblistClause>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<DefaultClause, LiblistClause>>>::type v5;
public:
	ConfigRuleStatement() { }
	boost::make_variant_over<v5>::type choice;
};

class ConsecutiveRepetition
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ConstOrRangeExpression>>::type v1;
public:
	ConsecutiveRepetition() { }
	boost::make_variant_over<v1>::type choice;
};

class ConstIdentifier
{
public:
	ConstIdentifier() { }
	ConstIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class ConstOrRangeExpression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<CycleDelayConstRangeExpression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ConstantExpression>>::type v2;
public:
	ConstOrRangeExpression() { }
	boost::make_variant_over<v2>::type choice;
};

class ConstanLetExpression
{
public:
	ConstanLetExpression() { }
	ConstanLetExpression(LetExpression * _letExpression) { letExpression = _letExpression; }

	LetExpression *letExpression;
};
class ConstantAssignmentPatternExpression
{
public:
	ConstantAssignmentPatternExpression() { }
	ConstantAssignmentPatternExpression(AssignmentPatternExpression * _assignmentPatternExpression) { assignmentPatternExpression = _assignmentPatternExpression; }

	AssignmentPatternExpression *assignmentPatternExpression;
};
class ConstantBitSelect
{
public:
	ConstantBitSelect() { }
	ConstantBitSelect(ConstantExpression * _constantExpression) { constantExpression = _constantExpression; }

	ConstantExpression *constantExpression;
};
class ConstantCast
{
public:
	ConstantCast() { }
	ConstantCast(CastingType * _castingType, ConstantExpression * _constantExpression) { castingType = _castingType; constantExpression = _constantExpression; }

	CastingType *castingType;
	ConstantExpression *constantExpression;
};

class ConstantConcatenation
{
public:
	ConstantConcatenation() { }
	ConstantConcatenation(std::vector<ConstantExpression> * _constantExpression) { constantExpression = _constantExpression; }

	std::vector<ConstantExpression> *constantExpression;
};

class ConstantExpression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<ConstantExpression, std::vector<AttributeInstance>, ConstantExpression, ConstantExpression>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<ConstantExpression, BinaryOperator, std::vector<AttributeInstance>, ConstantExpression>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<UnaryOperator, std::vector<AttributeInstance>, ConstantPrimary>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<ConstantPrimary>>::type v4;
public:
	ConstantExpression() { }
	boost::make_variant_over<v4>::type choice;
};

class ConstantFunctionCall
{
public:
	ConstantFunctionCall() { }
	ConstantFunctionCall(FunctionSubroutineCall * _functionSubroutineCall) { functionSubroutineCall = _functionSubroutineCall; }

	FunctionSubroutineCall *functionSubroutineCall;
};
class ConstantIndexedRange
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<ConstantExpression, ConstantExpression>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<ConstantExpression, ConstantExpression>>>::type v2;
public:
	ConstantIndexedRange() { }
	boost::make_variant_over<v2>::type choice;
};

class ConstantMintypmaxExpression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ConstantExpression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<ConstantExpression, ConstantExpression, ConstantExpression>>>::type v2;
public:
	ConstantMintypmaxExpression() { }
	boost::make_variant_over<v2>::type choice;
};

class ConstantMultipleConcatenation
{
public:
	ConstantMultipleConcatenation() { }
	ConstantMultipleConcatenation(ConstantExpression * _constantExpression, ConstantConcatenation * _constantConcatenation) { constantExpression = _constantExpression; constantConcatenation = _constantConcatenation; }

	ConstantExpression *constantExpression;
	ConstantConcatenation *constantConcatenation;
};

class ConstantParamExpression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<DataType>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ConstantMintypmaxExpression>>::type v2;
public:
	ConstantParamExpression() { }
	boost::make_variant_over<v2>::type choice;
};

class ConstantPartSelectRange
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ConstantIndexedRange>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ConstantRange>>::type v2;
public:
	ConstantPartSelectRange() { }
	boost::make_variant_over<v2>::type choice;
};

class ConstantPrimary
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<TypeReference>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ConstantAssignmentPatternExpression>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<ConstantCast>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<ConstantMintypmaxExpression>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<ConstanLetExpression>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<ConstantFunctionCall>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<std::tuple<ConstantMultipleConcatenation, std::optional<ConstantRangeExpression>>>>::type v7;
	typedef boost::mpl::push_front<v7, boost::recursive_wrapper<std::tuple<ConstantConcatenation, std::optional<ConstantRangeExpression>>>>::type v8;
	typedef boost::mpl::push_front<v8, boost::recursive_wrapper<std::tuple<std::optional<ClassScope>, EnumIdentifier>>>::type v9;
	typedef boost::mpl::push_front<v9, boost::recursive_wrapper<std::tuple<std::optional<PackageScope>, EnumIdentifier>>>::type v10;
	typedef boost::mpl::push_front<v10, boost::recursive_wrapper<std::tuple<FormalPortIdentifier, ConstantSelect>>>::type v11;
	typedef boost::mpl::push_front<v11, boost::recursive_wrapper<GenvarIdentifier>>::type v12;
	typedef boost::mpl::push_front<v12, boost::recursive_wrapper<std::tuple<SpecparamIdentifier, std::optional<ConstantRangeExpression>>>>::type v13;
	typedef boost::mpl::push_front<v13, boost::recursive_wrapper<std::tuple<PsParameterIdentifier, ConstantSelect>>>::type v14;
	typedef boost::mpl::push_front<v14, boost::recursive_wrapper<PrimaryLiteral>>::type v15;
public:
	ConstantPrimary() { }
	boost::make_variant_over<v15>::type choice;
};

class ConstantRange
{
public:
	ConstantRange() { }
	ConstantRange(ConstantExpression * _constantExpression0, ConstantExpression * _constantExpression1) { constantExpression0 = _constantExpression0; constantExpression1 = _constantExpression1; }

	ConstantExpression *constantExpression0;
	ConstantExpression *constantExpression1;
};

class ConstantRangeExpression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ConstantPartSelectRange>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ConstantExpression>>::type v2;
public:
	ConstantRangeExpression() { }
	boost::make_variant_over<v2>::type choice;
};

class ConstantSelect
{
public:
	ConstantSelect() { }
	ConstantSelect(std::optional<std::tuple<std::vector<std::tuple<MemberIdentifier, ConstantBitSelect>>, MemberIdentifier>> * _memberIdentifier, ConstantBitSelect * _constantBitSelect, std::optional<ConstantPartSelectRange> * _constantPartSelectRange) { memberIdentifier = _memberIdentifier; constantBitSelect = _constantBitSelect; constantPartSelectRange = _constantPartSelectRange; }

	std::optional<std::tuple<std::vector<std::tuple<MemberIdentifier, ConstantBitSelect>>, MemberIdentifier>> *memberIdentifier;
	ConstantBitSelect *constantBitSelect;
	std::optional<ConstantPartSelectRange> *constantPartSelectRange;
};

class ConstraintBlock
{
public:
	ConstraintBlock() { }
	ConstraintBlock(std::vector<ConstraintBlockItem> * _constraintBlockItem) { constraintBlockItem = _constraintBlockItem; }

	std::vector<ConstraintBlockItem> *constraintBlockItem;
};

class ConstraintBlockItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ConstraintExpression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<SolveBeforeList, SolveBeforeList>>>::type v2;
public:
	ConstraintBlockItem() { }
	boost::make_variant_over<v2>::type choice;
};

class ConstraintDeclaration
{
public:
	ConstraintDeclaration() { }
	ConstraintDeclaration(ContraintIdentifier * _contraintIdentifier, ConstraintBlock * _constraintBlock) { contraintIdentifier = _contraintIdentifier; constraintBlock = _constraintBlock; }

	ContraintIdentifier *contraintIdentifier;
	ConstraintBlock *constraintBlock;
};

class ConstraintExpression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ConstraintPrimary>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<PsOrHierarchicalArrayIdentifier, std::optional<LoopVariables>, ConstraintSet>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<Expression, ConstraintSet, std::optional<ConstraintSet>>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<Expression, ConstraintSet>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<UniquenessConstraint>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<ExpressionOrDist>>::type v6;
public:
	ConstraintExpression() { }
	boost::make_variant_over<v6>::type choice;
};

class ConstraintPrimary
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<ClassScope>, HierarchicalIdentifier, Select>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<ImplicitClassHandle>, HierarchicalIdentifier, Select>>>::type v2;
public:
	ConstraintPrimary() { }
	boost::make_variant_over<v2>::type choice;
};

enum class ConstraintPrototypeQualifier
{
	Extern, Pure
};

class ConstraintSet
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::vector<ConstraintExpression>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ConstraintExpression>>::type v2;
public:
	ConstraintSet() { }
	boost::make_variant_over<v2>::type choice;
};

class ContinuousAssign
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<DelayControl>, ListOfVariableAssignments>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<DriveStrength>, std::optional<Delay3>, ListOfNetAssignments>>>::type v2;
public:
	ContinuousAssign() { }
	boost::make_variant_over<v2>::type choice;
};

class ContraintIdentifier
{
public:
	ContraintIdentifier() { }
	ContraintIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class ContraintPrototype
{
public:
	ContraintPrototype() { }
	ContraintPrototype(std::optional<ConstraintPrototypeQualifier> * _constraintPrototypeQualifier, ContraintIdentifier * _contraintIdentifier) { constraintPrototypeQualifier = _constraintPrototypeQualifier; contraintIdentifier = _contraintIdentifier; }

	std::optional<ConstraintPrototypeQualifier> *constraintPrototypeQualifier;
	ContraintIdentifier *contraintIdentifier;
};

class ControlledReferenceEvent
{
public:
	ControlledReferenceEvent() { }
	ControlledReferenceEvent(ControlledTimingCheckEvent * _controlledTimingCheckEvent) { controlledTimingCheckEvent = _controlledTimingCheckEvent; }

	ControlledTimingCheckEvent *controlledTimingCheckEvent;
};
class ControlledTimingCheckEvent
{
public:
	ControlledTimingCheckEvent() { }
	ControlledTimingCheckEvent(TimingCheckEventControl * _timingCheckEventControl, SpecifyTerminalDescriptor * _specifyTerminalDescriptor, std::optional<TimingCheckCondition> * _timingCheckCondition) { timingCheckEventControl = _timingCheckEventControl; specifyTerminalDescriptor = _specifyTerminalDescriptor; timingCheckCondition = _timingCheckCondition; }

	TimingCheckEventControl *timingCheckEventControl;
	SpecifyTerminalDescriptor *specifyTerminalDescriptor;
	std::optional<TimingCheckCondition> *timingCheckCondition;
};

class CoverCross
{
public:
	CoverCross() { }
	CoverCross(std::optional<CrossIdentifier> * _crossIdentifier, ListOfCrossItems * _listOfCrossItems, std::optional<Expression> * _expression, CrossBody * _crossBody) { crossIdentifier = _crossIdentifier; listOfCrossItems = _listOfCrossItems; expression = _expression; crossBody = _crossBody; }

	std::optional<CrossIdentifier> *crossIdentifier;
	ListOfCrossItems *listOfCrossItems;
	std::optional<Expression> *expression;
	CrossBody *crossBody;
};

class CoverPoint
{
public:
	CoverPoint() { }
	CoverPoint(std::optional<std::tuple<std::optional<DataTypeOrImplicit>, CoverPointIdentifier>> * _dataTypeOrImplicit, Expression * _expression1, std::optional<Expression> * _expression2, BinsOrEmpty * _binsOrEmpty) { dataTypeOrImplicit = _dataTypeOrImplicit; expression1 = _expression1; expression2 = _expression2; binsOrEmpty = _binsOrEmpty; }

	std::optional<std::tuple<std::optional<DataTypeOrImplicit>, CoverPointIdentifier>> *dataTypeOrImplicit;
	Expression *expression1;
	std::optional<Expression> *expression2;
	BinsOrEmpty *binsOrEmpty;
};

class CoverPointIdentifier
{
public:
	CoverPointIdentifier() { }
	CoverPointIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class CoverPropertyStatement
{
public:
	CoverPropertyStatement() { }
	CoverPropertyStatement(PropertySpec * _propertySpec, StatementOrNull * _statementOrNull) { propertySpec = _propertySpec; statementOrNull = _statementOrNull; }

	PropertySpec *propertySpec;
	StatementOrNull *statementOrNull;
};

class CoverSequenceStatement
{
public:
	CoverSequenceStatement() { }
	CoverSequenceStatement(std::optional<ClockingEvent> * _clockingEvent, std::optional<ExpressionOrDist> * _expressionOrDist, SequenceExpr * _sequenceExpr, StatementOrNull * _statementOrNull) { clockingEvent = _clockingEvent; expressionOrDist = _expressionOrDist; sequenceExpr = _sequenceExpr; statementOrNull = _statementOrNull; }

	std::optional<ClockingEvent> *clockingEvent;
	std::optional<ExpressionOrDist> *expressionOrDist;
	SequenceExpr *sequenceExpr;
	StatementOrNull *statementOrNull;
};

class CoverageEvent
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<BlockEventExpression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::optional<TfPortList>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<ClockingEvent>>::type v3;
public:
	CoverageEvent() { }
	boost::make_variant_over<v3>::type choice;
};

class CoverageOption
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<MemberIdentifier, Expression>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<MemberIdentifier, Expression>>>::type v2;
public:
	CoverageOption() { }
	boost::make_variant_over<v2>::type choice;
};

class CoverageSpec
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<CoverCross>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<CoverPoint>>::type v2;
public:
	CoverageSpec() { }
	boost::make_variant_over<v2>::type choice;
};

class CoverageSpecOrOption
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, CoverageOption>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, CoverageSpec>>>::type v2;
public:
	CoverageSpecOrOption() { }
	boost::make_variant_over<v2>::type choice;
};

class CovergroupDeclaration
{
public:
	CovergroupDeclaration() { }
	CovergroupDeclaration(CovergroupIdentifier * _covergroupIdentifier0, std::optional<std::optional<TfPortList>> * _tfPortList, std::optional<CoverageEvent> * _coverageEvent, std::vector<CoverageSpecOrOption> * _coverageSpecOrOption, std::optional<CovergroupIdentifier> * _covergroupIdentifier4) { covergroupIdentifier0 = _covergroupIdentifier0; tfPortList = _tfPortList; coverageEvent = _coverageEvent; coverageSpecOrOption = _coverageSpecOrOption; covergroupIdentifier4 = _covergroupIdentifier4; }

	CovergroupIdentifier *covergroupIdentifier0;
	std::optional<std::optional<TfPortList>> *tfPortList;
	std::optional<CoverageEvent> *coverageEvent;
	std::vector<CoverageSpecOrOption> *coverageSpecOrOption;
	std::optional<CovergroupIdentifier> *covergroupIdentifier4;
};

class CovergroupExpression
{
public:
	CovergroupExpression() { }
	CovergroupExpression(Expression * _expression) { expression = _expression; }

	Expression *expression;
};
class CovergroupIdentifier
{
public:
	CovergroupIdentifier() { }
	CovergroupIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class CovergroupRangeList
{
public:
	CovergroupRangeList() { }
	CovergroupRangeList(CovergroupValueRange * _covergroupValueRange) { covergroupValueRange = _covergroupValueRange; }

	CovergroupValueRange *covergroupValueRange;
};
class CovergroupValueRange
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<CovergroupExpression, CovergroupExpression>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<CovergroupExpression>>::type v2;
public:
	CovergroupValueRange() { }
	boost::make_variant_over<v2>::type choice;
};

class CrossBody
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::vector<CrossBodyItem>>>::type v1;
public:
	CrossBody() { }
	boost::make_variant_over<v1>::type choice;
};

class CrossBodyItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<BinsSelectionOrOption>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<FunctionDeclaration>>::type v2;
public:
	CrossBodyItem() { }
	boost::make_variant_over<v2>::type choice;
};

class CrossIdentifier
{
public:
	CrossIdentifier() { }
	CrossIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class CrossItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<VariableIdentifier>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<CoverPointIdentifier>>::type v2;
public:
	CrossItem() { }
	boost::make_variant_over<v2>::type choice;
};

class CrossSetExpression
{
public:
	CrossSetExpression() { }
	CrossSetExpression(CovergroupExpression * _covergroupExpression) { covergroupExpression = _covergroupExpression; }

	CovergroupExpression *covergroupExpression;
};
class CurrentState
{
public:
	CurrentState() { }
	CurrentState(LevelSymbol * _levelSymbol) { levelSymbol = _levelSymbol; }

	LevelSymbol *levelSymbol;
};
class CycleDelay
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<Expression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<Identifier>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<IntegralNumber>>::type v3;
public:
	CycleDelay() { }
	boost::make_variant_over<v3>::type choice;
};

class CycleDelayConstRangeExpression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<ConstantExpression, ConstantExpression>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ConstantExpression>>::type v2;
public:
	CycleDelayConstRangeExpression() { }
	boost::make_variant_over<v2>::type choice;
};

class CycleDelayRange
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<CycleDelayConstRangeExpression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ConstantPrimary>>::type v2;
public:
	CycleDelayRange() { }
	boost::make_variant_over<v2>::type choice;
};

class DataDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<PackageImportDeclaration, NetTypeDeclaration>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<TypeDeclaration>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::optional<Lifetime>, DataTypeOrImplicit, ListOfVariableDeclAssignments>>>::type v3;
public:
	DataDeclaration() { }
	boost::make_variant_over<v3>::type choice;
};

class DataEvent
{
public:
	DataEvent() { }
	DataEvent(TimingCheckEvent * _timingCheckEvent) { timingCheckEvent = _timingCheckEvent; }

	TimingCheckEvent *timingCheckEvent;
};
class DataSourceExpression
{
public:
	DataSourceExpression() { }
	DataSourceExpression(Expression * _expression) { expression = _expression; }

	Expression *expression;
};
class DataType
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<TypeReference>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<PsCovergroupIdentifier>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<ClassType>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<std::optional<PackageScope>, TypeIdentifier, std::vector<PackedDimension>>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<std::optional<ClassScope>, TypeIdentifier, std::vector<PackedDimension>>>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<std::tuple<InterfaceIdentifier, std::optional<ParameterValueAssignment>, std::optional<ModportIdentifier>>>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<std::tuple<std::optional<EnumBaseType>, std::vector<EnumNameDeclaration>, std::vector<PackedDimension>>>>::type v7;
	typedef boost::mpl::push_front<v7, boost::recursive_wrapper<std::tuple<StructUnion, std::optional<std::optional<Signing>>, std::vector<StructUnionMember>, std::vector<PackedDimension>>>>::type v8;
	typedef boost::mpl::push_front<v8, boost::recursive_wrapper<NonIntegerType>>::type v9;
	typedef boost::mpl::push_front<v9, boost::recursive_wrapper<std::tuple<IntegerAtomType, std::optional<Signing>>>>::type v10;
	typedef boost::mpl::push_front<v10, boost::recursive_wrapper<std::tuple<IntegerVectorType, std::optional<Signing>, std::vector<PackedDimension>>>>::type v11;
public:
	DataType() { }
	boost::make_variant_over<v11>::type choice;
};

class DataTypeOrImplicit
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ImplicitDataType>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<DataType>>::type v2;
public:
	DataTypeOrImplicit() { }
	boost::make_variant_over<v2>::type choice;
};

class DataTypeOrVoid
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<DataType>>::type v1;
public:
	DataTypeOrVoid() { }
	boost::make_variant_over<v1>::type choice;
};

typedef std::string DecimalBase;
class DecimalNumber
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<Size>, DecimalBase>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<Size>, DecimalBase>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::optional<Size>, DecimalBase, UnsignedNumber>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<UnsignedNumber>>::type v4;
public:
	DecimalNumber() { }
	boost::make_variant_over<v4>::type choice;
};

enum class DefaultClause
{
	Default
};

class DefaultSkew
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<ClockingSkew, ClockingSkew>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ClockingSkew>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<ClockingSkew>>::type v3;
public:
	DefaultSkew() { }
	boost::make_variant_over<v3>::type choice;
};

class DeferredImmediateAssertStatement
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<UnsignedNumber, Expression, ActionBlock>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<Expression, ActionBlock>>>::type v2;
public:
	DeferredImmediateAssertStatement() { }
	boost::make_variant_over<v2>::type choice;
};

class DeferredImmediateAssertionItem
{
public:
	DeferredImmediateAssertionItem() { }
	DeferredImmediateAssertionItem(std::optional<BlockIdentifier> * _blockIdentifier, DeferredImmediateAssertionStatement * _deferredImmediateAssertionStatement) { blockIdentifier = _blockIdentifier; deferredImmediateAssertionStatement = _deferredImmediateAssertionStatement; }

	std::optional<BlockIdentifier> *blockIdentifier;
	DeferredImmediateAssertionStatement *deferredImmediateAssertionStatement;
};

class DeferredImmediateAssertionStatement
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<DeferredImmediateCoverStatement>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<DeferredImmediateAssumeStatement>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<DeferredImmediateAssertStatement>>::type v3;
public:
	DeferredImmediateAssertionStatement() { }
	boost::make_variant_over<v3>::type choice;
};

class DeferredImmediateAssumeStatement
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<UnsignedNumber, Expression, ActionBlock>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<Expression, ActionBlock>>>::type v2;
public:
	DeferredImmediateAssumeStatement() { }
	boost::make_variant_over<v2>::type choice;
};

class DeferredImmediateCoverStatement
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<UnsignedNumber, Expression, StatementOrNull>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<Expression, StatementOrNull>>>::type v2;
public:
	DeferredImmediateCoverStatement() { }
	boost::make_variant_over<v2>::type choice;
};

class DefparamAssignment
{
public:
	DefparamAssignment() { }
	DefparamAssignment(HierarchicalParameterIdentifier * _hierarchicalParameterIdentifier, ConstantMintypmaxExpression * _constantMintypmaxExpression) { hierarchicalParameterIdentifier = _hierarchicalParameterIdentifier; constantMintypmaxExpression = _constantMintypmaxExpression; }

	HierarchicalParameterIdentifier *hierarchicalParameterIdentifier;
	ConstantMintypmaxExpression *constantMintypmaxExpression;
};

class Delay2
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<MintypmaxExpression, std::optional<MintypmaxExpression>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<DelayValue>>::type v2;
public:
	Delay2() { }
	boost::make_variant_over<v2>::type choice;
};

class Delay3
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<MintypmaxExpression, std::optional<std::tuple<MintypmaxExpression, std::optional<MintypmaxExpression>>>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<DelayValue>>::type v2;
public:
	Delay3() { }
	boost::make_variant_over<v2>::type choice;
};

class DelayControl
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<MintypmaxExpression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<DelayValue>>::type v2;
public:
	DelayControl() { }
	boost::make_variant_over<v2>::type choice;
};

class DelayOrEventControl
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<Expression, EventControl>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<EventControl>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<DelayControl>>::type v3;
public:
	DelayOrEventControl() { }
	boost::make_variant_over<v3>::type choice;
};

class DelayValue
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<TimeLiteral>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<PsIdentifier>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<RealNumber>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<UnsignedNumber>>::type v4;
public:
	DelayValue() { }
	boost::make_variant_over<v4>::type choice;
};

class DelayedData
{
public:
	DelayedData() { }
	DelayedData(TerminalIdentifier * _terminalIdentifier, std::optional<ConstantMintypmaxExpression> * _constantMintypmaxExpression) { terminalIdentifier = _terminalIdentifier; constantMintypmaxExpression = _constantMintypmaxExpression; }

	TerminalIdentifier *terminalIdentifier;
	std::optional<ConstantMintypmaxExpression> *constantMintypmaxExpression;
};

class DelayedReference
{
public:
	DelayedReference() { }
	DelayedReference(TerminalIdentifier * _terminalIdentifier, std::optional<ConstantMintypmaxExpression> * _constantMintypmaxExpression) { terminalIdentifier = _terminalIdentifier; constantMintypmaxExpression = _constantMintypmaxExpression; }

	TerminalIdentifier *terminalIdentifier;
	std::optional<ConstantMintypmaxExpression> *constantMintypmaxExpression;
};

class Description
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ConfigDeclaration>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, BindDirective>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, PackageItem>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<PackageDeclaration>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<ProgramDeclaration>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<InterfaceDeclaration>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<UdpDeclaration>>::type v7;
	typedef boost::mpl::push_front<v7, boost::recursive_wrapper<ModuleDeclaration>>::type v8;
public:
	Description() { }
	boost::make_variant_over<v8>::type choice;
};

class DesignStatement
{
public:
	DesignStatement() { }
	DesignStatement(std::vector<std::tuple<std::optional<LibraryIdentifier>, CellIdentifier>> * _libraryIdentifier) { libraryIdentifier = _libraryIdentifier; }

	std::vector<std::tuple<std::optional<LibraryIdentifier>, CellIdentifier>> *libraryIdentifier;
};

class DisableStatement
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<HierarchicalBlockIdentifier>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<HierarchicalTaskIdentifier>>::type v2;
public:
	DisableStatement() { }
	boost::make_variant_over<v2>::type choice;
};

class DistItem
{
public:
	DistItem() { }
	DistItem(ValueRange * _valueRange, std::optional<DistWeight> * _distWeight) { valueRange = _valueRange; distWeight = _distWeight; }

	ValueRange *valueRange;
	std::optional<DistWeight> *distWeight;
};

class DistList
{
public:
	DistList() { }
	DistList(DistItem * _distItem) { distItem = _distItem; }

	DistItem *distItem;
};
class DistWeight
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<Expression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<Expression>>::type v2;
public:
	DistWeight() { }
	boost::make_variant_over<v2>::type choice;
};

enum class DpiFunctionImportProperty
{
	Context, Pure
};

class DpiFunctionProto
{
public:
	DpiFunctionProto() { }
	DpiFunctionProto(FunctionPrototype * _functionPrototype) { functionPrototype = _functionPrototype; }

	FunctionPrototype *functionPrototype;
};
class DpiImportExport
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<DpiSpecString, std::optional<CIdentifier>, TaskIdentifier>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<DpiSpecString, std::optional<CIdentifier>, FunctionIdentifier>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<DpiSpecString, std::optional<DpiTaskImportProperty>, std::optional<CIdentifier>, DpiTaskProto>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<DpiSpecString, std::optional<DpiFunctionImportProperty>, std::optional<CIdentifier>, DpiFunctionProto>>>::type v4;
public:
	DpiImportExport() { }
	boost::make_variant_over<v4>::type choice;
};

class DpiSpecString
{
public:
	DpiSpecString() { }
	DpiSpecString(StringLiteral * _stringLiteral) { stringLiteral = _stringLiteral; }

	StringLiteral *stringLiteral;
};
enum class DpiTaskImportProperty
{
	Context
};

class DpiTaskProto
{
public:
	DpiTaskProto() { }
	DpiTaskProto(TaskPrototype * _taskPrototype) { taskPrototype = _taskPrototype; }

	TaskPrototype *taskPrototype;
};
class DriveStrength
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<Strength1, Strength0>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<Strength0, Strength1>>>::type v2;
public:
	DriveStrength() { }
	boost::make_variant_over<v2>::type choice;
};

class DynamicArrayNew
{
public:
	DynamicArrayNew() { }
	DynamicArrayNew(Expression * _expression0, std::optional<Expression> * _expression1) { expression0 = _expression0; expression1 = _expression1; }

	Expression *expression0;
	std::optional<Expression> *expression1;
};

class DynamicArrayVariableIdentifier
{
public:
	DynamicArrayVariableIdentifier() { }
	DynamicArrayVariableIdentifier(VariableIdentifier * _variableIdentifier) { variableIdentifier = _variableIdentifier; }

	VariableIdentifier *variableIdentifier;
};
class EdgeControlSpecifier
{
public:
	EdgeControlSpecifier() { }
	EdgeControlSpecifier(std::vector<EdgeDescriptor> * _edgeDescriptor) { edgeDescriptor = _edgeDescriptor; }

	std::vector<EdgeDescriptor> *edgeDescriptor;
};

class EdgeDescriptor
{
public:
	EdgeDescriptor() { }
	EdgeDescriptor(Number * _number) { number = _number; }

	Number *number;
};
enum class EdgeIdentifier
{
	Posedge, Negedge, Edge
};

class EdgeIndicator
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<EdgeSymbol>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<LevelSymbol, LevelSymbol>>>::type v2;
public:
	EdgeIndicator() { }
	boost::make_variant_over<v2>::type choice;
};

class EdgeInputList
{
public:
	EdgeInputList() { }
	EdgeInputList(std::vector<LevelSymbol> * _levelSymbol0, EdgeIndicator * _edgeIndicator, std::vector<LevelSymbol> * _levelSymbol2) { levelSymbol0 = _levelSymbol0; edgeIndicator = _edgeIndicator; levelSymbol2 = _levelSymbol2; }

	std::vector<LevelSymbol> *levelSymbol0;
	EdgeIndicator *edgeIndicator;
	std::vector<LevelSymbol> *levelSymbol2;
};

class EdgeSensitivePathDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<FullEdgeSensitivePathDescription, PathDelayValue>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<ParallelEdgeSensitivePathDescription, PathDelayValue>>>::type v2;
public:
	EdgeSensitivePathDeclaration() { }
	boost::make_variant_over<v2>::type choice;
};

class EdgeSymbol
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<Identifier>>::type v1;
public:
	EdgeSymbol() { }
	boost::make_variant_over<v1>::type choice;
};

class ElaborationSystemTask
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::optional<std::optional<ListOfArguments>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::optional<std::tuple<FinishNumber, std::optional<ListOfArguments>>>>>::type v2;
public:
	ElaborationSystemTask() { }
	boost::make_variant_over<v2>::type choice;
};

enum class EmptyQueue
{
	Lbracket, Rbracket
};

class EnableGateInstance
{
public:
	EnableGateInstance() { }
	EnableGateInstance(std::optional<NameOfInstance> * _nameOfInstance, OutputTerminal * _outputTerminal, InputTerminal * _inputTerminal, EnableTerminal * _enableTerminal) { nameOfInstance = _nameOfInstance; outputTerminal = _outputTerminal; inputTerminal = _inputTerminal; enableTerminal = _enableTerminal; }

	std::optional<NameOfInstance> *nameOfInstance;
	OutputTerminal *outputTerminal;
	InputTerminal *inputTerminal;
	EnableTerminal *enableTerminal;
};

enum class EnableGatetype
{
	Bufif0, Bufif1, Notif0, Notif1
};

class EnableTerminal
{
public:
	EnableTerminal() { }
	EnableTerminal(Expression * _expression) { expression = _expression; }

	Expression *expression;
};
class EndEdgeOffset
{
public:
	EndEdgeOffset() { }
	EndEdgeOffset(MintypmaxExpression * _mintypmaxExpression) { mintypmaxExpression = _mintypmaxExpression; }

	MintypmaxExpression *mintypmaxExpression;
};
class EnumBaseType
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<TypeIdentifier, std::optional<PackedDimension>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<IntegerVectorType, std::optional<Signing>, std::optional<PackedDimension>>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<IntegerAtomType, std::optional<Signing>>>>::type v3;
public:
	EnumBaseType() { }
	boost::make_variant_over<v3>::type choice;
};

class EnumIdentifier
{
public:
	EnumIdentifier() { }
	EnumIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class EnumNameDeclaration
{
public:
	EnumNameDeclaration() { }
	EnumNameDeclaration(EnumIdentifier * _enumIdentifier, std::optional<std::tuple<IntegralNumber, std::optional<IntegralNumber>>> * _integralNumber, std::optional<ConstantExpression> * _constantExpression) { enumIdentifier = _enumIdentifier; integralNumber = _integralNumber; constantExpression = _constantExpression; }

	EnumIdentifier *enumIdentifier;
	std::optional<std::tuple<IntegralNumber, std::optional<IntegralNumber>>> *integralNumber;
	std::optional<ConstantExpression> *constantExpression;
};

class ErrorLimitValue
{
public:
	ErrorLimitValue() { }
	ErrorLimitValue(LimitValue * _limitValue) { limitValue = _limitValue; }

	LimitValue *limitValue;
};
class EventBasedFlag
{
public:
	EventBasedFlag() { }
	EventBasedFlag(ConstantExpression * _constantExpression) { constantExpression = _constantExpression; }

	ConstantExpression *constantExpression;
};
class EventControl
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<PsOrHierarchicalSequenceIdentifier>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<EventExpression>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<HierarchicalEventIdentifier>>::type v3;
public:
	EventControl() { }
	boost::make_variant_over<v3>::type choice;
};

class EventExpression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<EventExpression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<EventExpression, EventExpression>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<EventExpression, EventExpression>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<SequenceInstance, std::optional<Expression>>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<std::optional<EdgeIdentifier>, Expression, std::optional<Expression>>>>::type v5;
public:
	EventExpression() { }
	boost::make_variant_over<v5>::type choice;
};

class EventTrigger
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<DelayOrEventControl>, HierarchicalEventIdentifier>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<HierarchicalEventIdentifier>>::type v2;
public:
	EventTrigger() { }
	boost::make_variant_over<v2>::type choice;
};

class ExpectPropertyStatement
{
public:
	ExpectPropertyStatement() { }
	ExpectPropertyStatement(PropertySpec * _propertySpec, ActionBlock * _actionBlock) { propertySpec = _propertySpec; actionBlock = _actionBlock; }

	PropertySpec *propertySpec;
	ActionBlock *actionBlock;
};

class Expression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<TaggedUnionExpression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<InsideExpression>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<ConditionalExpression>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<Expression, BinaryOperator, std::vector<AttributeInstance>, Expression>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<OperatorAssignment>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<IncOrDecExpression>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<std::tuple<UnaryOperator, std::vector<AttributeInstance>, Primary>>>::type v7;
	typedef boost::mpl::push_front<v7, boost::recursive_wrapper<Primary>>::type v8;
public:
	Expression() { }
	boost::make_variant_over<v8>::type choice;
};

class ExpressionOrCondPattern
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<CondPattern>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<Expression>>::type v2;
public:
	ExpressionOrCondPattern() { }
	boost::make_variant_over<v2>::type choice;
};

class ExpressionOrDist
{
public:
	ExpressionOrDist() { }
	ExpressionOrDist(Expression * _expression, std::optional<DistList> * _distList) { expression = _expression; distList = _distList; }

	Expression *expression;
	std::optional<DistList> *distList;
};

class ExternConstraintDeclaration
{
public:
	ExternConstraintDeclaration() { }
	ExternConstraintDeclaration(ClassScope * _classScope, ContraintIdentifier * _contraintIdentifier, ConstraintBlock * _constraintBlock) { classScope = _classScope; contraintIdentifier = _contraintIdentifier; constraintBlock = _constraintBlock; }

	ClassScope *classScope;
	ContraintIdentifier *contraintIdentifier;
	ConstraintBlock *constraintBlock;
};

class ExternTfDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<TaskPrototype>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<MethodPrototype>>::type v2;
public:
	ExternTfDeclaration() { }
	boost::make_variant_over<v2>::type choice;
};

class FilePathSpec
{
public:
	FilePathSpec() { }
	FilePathSpec(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class FinalConstruct
{
public:
	FinalConstruct() { }
	FinalConstruct(FunctionStatement * _functionStatement) { functionStatement = _functionStatement; }

	FunctionStatement *functionStatement;
};

class FinishNumber
{
public:
	FinishNumber() { }
	FinishNumber(UnsignedNumber * _unsignedNumber) { unsignedNumber = _unsignedNumber; }

	UnsignedNumber *unsignedNumber;
};
class FixedPointNumber
{
public:
	FixedPointNumber() { }
	FixedPointNumber(UnsignedNumber * _unsignedNumber0, UnsignedNumber * _unsignedNumber1) { unsignedNumber0 = _unsignedNumber0; unsignedNumber1 = _unsignedNumber1; }

	UnsignedNumber *unsignedNumber0;
	UnsignedNumber *unsignedNumber1;
};

class ForInitialization
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::vector<ForVariableDeclaration>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ListOfVariableAssignments>>::type v2;
public:
	ForInitialization() { }
	boost::make_variant_over<v2>::type choice;
};

class ForStep
{
public:
	ForStep() { }
	ForStep(ForStepAssignment * _forStepAssignment) { forStepAssignment = _forStepAssignment; }

	ForStepAssignment *forStepAssignment;
};
class ForStepAssignment
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<FunctionSubroutineCall>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<IncOrDecExpression>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<OperatorAssignment>>::type v3;
public:
	ForStepAssignment() { }
	boost::make_variant_over<v3>::type choice;
};

class ForVariableDeclaration
{
public:
	ForVariableDeclaration() { }
	ForVariableDeclaration(DataType * _dataType, std::vector<std::tuple<VariableIdentifier, Expression>> * _variableIdentifier) { dataType = _dataType; variableIdentifier = _variableIdentifier; }

	DataType *dataType;
	std::vector<std::tuple<VariableIdentifier, Expression>> *variableIdentifier;
};

class FormalPortIdentifier
{
public:
	FormalPortIdentifier() { }
	FormalPortIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class FullEdgeSensitivePathDescription
{
public:
	FullEdgeSensitivePathDescription() { }
	FullEdgeSensitivePathDescription(std::optional<EdgeIdentifier> * _edgeIdentifier, ListOfPathInputs * _listOfPathInputs, std::optional<PolarityOperator> * _polarityOperator2, ListOfPathOutputs * _listOfPathOutputs, std::optional<PolarityOperator> * _polarityOperator4, DataSourceExpression * _dataSourceExpression) { edgeIdentifier = _edgeIdentifier; listOfPathInputs = _listOfPathInputs; polarityOperator2 = _polarityOperator2; listOfPathOutputs = _listOfPathOutputs; polarityOperator4 = _polarityOperator4; dataSourceExpression = _dataSourceExpression; }

	std::optional<EdgeIdentifier> *edgeIdentifier;
	ListOfPathInputs *listOfPathInputs;
	std::optional<PolarityOperator> *polarityOperator2;
	ListOfPathOutputs *listOfPathOutputs;
	std::optional<PolarityOperator> *polarityOperator4;
	DataSourceExpression *dataSourceExpression;
};

class FullPathDescription
{
public:
	FullPathDescription() { }
	FullPathDescription(ListOfPathInputs * _listOfPathInputs, std::optional<PolarityOperator> * _polarityOperator, ListOfPathOutputs * _listOfPathOutputs) { listOfPathInputs = _listOfPathInputs; polarityOperator = _polarityOperator; listOfPathOutputs = _listOfPathOutputs; }

	ListOfPathInputs *listOfPathInputs;
	std::optional<PolarityOperator> *polarityOperator;
	ListOfPathOutputs *listOfPathOutputs;
};

class FullskewTimingCheck
{
public:
	FullskewTimingCheck() { }
	FullskewTimingCheck(ReferenceEvent * _referenceEvent, DataEvent * _dataEvent, TimingCheckLimit * _timingCheckLimit2, TimingCheckLimit * _timingCheckLimit3, std::optional<std::tuple<std::optional<Notifier>, std::optional<std::tuple<std::optional<EventBasedFlag>, std::optional<std::optional<RemainActiveFlag>>>>>> * _notifier) { referenceEvent = _referenceEvent; dataEvent = _dataEvent; timingCheckLimit2 = _timingCheckLimit2; timingCheckLimit3 = _timingCheckLimit3; notifier = _notifier; }

	ReferenceEvent *referenceEvent;
	DataEvent *dataEvent;
	TimingCheckLimit *timingCheckLimit2;
	TimingCheckLimit *timingCheckLimit3;
	std::optional<std::tuple<std::optional<Notifier>, std::optional<std::tuple<std::optional<EventBasedFlag>, std::optional<std::optional<RemainActiveFlag>>>>>> *notifier;
};

class FunctionBodyDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<FunctionDataTypeOrImplicit, std::optional<ClassScope>, FunctionIdentifier, std::optional<TfPortList>, std::vector<BlockItemDeclaration>, std::vector<FunctionStatementOrNull>, std::optional<FunctionIdentifier>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<FunctionDataTypeOrImplicit, std::optional<InterfaceIdentifier>, FunctionIdentifier, std::optional<TfPortList>, std::vector<BlockItemDeclaration>, std::vector<FunctionStatementOrNull>, std::optional<FunctionIdentifier>>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<FunctionDataTypeOrImplicit, std::optional<ClassScope>, FunctionIdentifier, std::vector<TfItemDeclaration>, std::vector<FunctionStatementOrNull>, std::optional<FunctionIdentifier>>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<FunctionDataTypeOrImplicit, std::optional<InterfaceIdentifier>, FunctionIdentifier, std::vector<TfItemDeclaration>, std::vector<FunctionStatementOrNull>, std::optional<FunctionIdentifier>>>>::type v4;
public:
	FunctionBodyDeclaration() { }
	boost::make_variant_over<v4>::type choice;
};

class FunctionDataTypeOrImplicit
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ImplicitDataType>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<DataTypeOrVoid>>::type v2;
public:
	FunctionDataTypeOrImplicit() { }
	boost::make_variant_over<v2>::type choice;
};

class FunctionDeclaration
{
public:
	FunctionDeclaration() { }
	FunctionDeclaration(std::optional<Lifetime> * _lifetime, FunctionBodyDeclaration * _functionBodyDeclaration) { lifetime = _lifetime; functionBodyDeclaration = _functionBodyDeclaration; }

	std::optional<Lifetime> *lifetime;
	FunctionBodyDeclaration *functionBodyDeclaration;
};

class FunctionIdentifier
{
public:
	FunctionIdentifier() { }
	FunctionIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class FunctionPrototype
{
public:
	FunctionPrototype() { }
	FunctionPrototype(DataTypeOrVoid * _dataTypeOrVoid, FunctionIdentifier * _functionIdentifier, std::optional<std::optional<TfPortList>> * _tfPortList) { dataTypeOrVoid = _dataTypeOrVoid; functionIdentifier = _functionIdentifier; tfPortList = _tfPortList; }

	DataTypeOrVoid *dataTypeOrVoid;
	FunctionIdentifier *functionIdentifier;
	std::optional<std::optional<TfPortList>> *tfPortList;
};

class FunctionStatement
{
public:
	FunctionStatement() { }
	FunctionStatement(Statement * _statement) { statement = _statement; }

	Statement *statement;
};
class FunctionStatementOrNull
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::vector<AttributeInstance>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<FunctionStatement>>::type v2;
public:
	FunctionStatementOrNull() { }
	boost::make_variant_over<v2>::type choice;
};

class FunctionSubroutineCall
{
public:
	FunctionSubroutineCall() { }
	FunctionSubroutineCall(SubroutineCall * _subroutineCall) { subroutineCall = _subroutineCall; }

	SubroutineCall *subroutineCall;
};
class GateInstantiation
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<PullupStrength>, std::vector<PullGateInstance>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<PulldownStrength>, std::vector<PullGateInstance>>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<PassSwitchtype, std::vector<PassSwitchInstance>>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<PassEnSwitchType, std::optional<Delay2>, std::vector<PassEnableSwitchInstance>>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<NOutputGatetype, std::optional<DriveStrength>, std::optional<Delay2>, std::vector<NOutputGateInstance>>>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<std::tuple<NInputGatetype, std::optional<DriveStrength>, std::optional<Delay2>, std::vector<NInputGateInstance>>>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<std::tuple<MosSwitchtype, std::optional<Delay3>, std::vector<MosSwitchInstance>>>>::type v7;
	typedef boost::mpl::push_front<v7, boost::recursive_wrapper<std::tuple<EnableGatetype, std::optional<DriveStrength>, std::optional<Delay3>, std::vector<EnableGateInstance>>>>::type v8;
	typedef boost::mpl::push_front<v8, boost::recursive_wrapper<std::tuple<CmosSwitchtype, std::optional<Delay3>, std::vector<CmosSwitchInstance>>>>::type v9;
public:
	GateInstantiation() { }
	boost::make_variant_over<v9>::type choice;
};

class GenerateBlock
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<GenerateBlockIdentifier>, std::optional<GenerateBlockIdentifier>, std::vector<GenerateItem>, std::optional<GenerateBlockIdentifier>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<GenerateItem>>::type v2;
public:
	GenerateBlock() { }
	boost::make_variant_over<v2>::type choice;
};

class GenerateBlockIdentifier
{
public:
	GenerateBlockIdentifier() { }
	GenerateBlockIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class GenerateItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<CheckerOrGenerateItem>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<InterfaceOrGenerateItem>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<ModuleOrGenerateItem>>::type v3;
public:
	GenerateItem() { }
	boost::make_variant_over<v3>::type choice;
};

class GenerateRegion
{
public:
	GenerateRegion() { }
	GenerateRegion(std::vector<GenerateItem> * _generateItem) { generateItem = _generateItem; }

	std::vector<GenerateItem> *generateItem;
};

class GenvarDeclaration
{
public:
	GenvarDeclaration() { }
	GenvarDeclaration(ListOfGenvarIdentifiers * _listOfGenvarIdentifiers) { listOfGenvarIdentifiers = _listOfGenvarIdentifiers; }

	ListOfGenvarIdentifiers *listOfGenvarIdentifiers;
};

class GenvarExpression
{
public:
	GenvarExpression() { }
	GenvarExpression(ConstantExpression * _constantExpression) { constantExpression = _constantExpression; }

	ConstantExpression *constantExpression;
};
class GenvarIdentifier
{
public:
	GenvarIdentifier() { }
	GenvarIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class GenvarInitialization
{
public:
	GenvarInitialization() { }
	GenvarInitialization(GenvarIdentifier * _genvarIdentifier, ConstantExpression * _constantExpression) { genvarIdentifier = _genvarIdentifier; constantExpression = _constantExpression; }

	GenvarIdentifier *genvarIdentifier;
	ConstantExpression *constantExpression;
};

class GenvarIteration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<GenvarIdentifier, IncOrDecOperator>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<IncOrDecOperator, GenvarIdentifier>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<GenvarIdentifier, AssignmentOperator, GenvarExpression>>>::type v3;
public:
	GenvarIteration() { }
	boost::make_variant_over<v3>::type choice;
};

class GotoRepetition
{
public:
	GotoRepetition() { }
	GotoRepetition(ConstOrRangeExpression * _constOrRangeExpression) { constOrRangeExpression = _constOrRangeExpression; }

	ConstOrRangeExpression *constOrRangeExpression;
};

typedef std::string HexBase;
class HexNumber
{
public:
	HexNumber() { }
	HexNumber(std::optional<Size> * _size, HexBase * _hexBase, HexValue * _hexValue) { size = _size; hexBase = _hexBase; hexValue = _hexValue; }

	std::optional<Size> *size;
	HexBase *hexBase;
	HexValue *hexValue;
};

typedef std::string HexValue;
class HierarchicalArrayIdentifier
{
public:
	HierarchicalArrayIdentifier() { }
	HierarchicalArrayIdentifier(HierarchicalIdentifier * _hierarchicalIdentifier) { hierarchicalIdentifier = _hierarchicalIdentifier; }

	HierarchicalIdentifier *hierarchicalIdentifier;
};
class HierarchicalBlockIdentifier
{
public:
	HierarchicalBlockIdentifier() { }
	HierarchicalBlockIdentifier(HierarchicalIdentifier * _hierarchicalIdentifier) { hierarchicalIdentifier = _hierarchicalIdentifier; }

	HierarchicalIdentifier *hierarchicalIdentifier;
};
class HierarchicalBtfIdentifier
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<ClassScope>, MethodIdentifier>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<HierarchicalIdentifier>, MethodIdentifier>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<HierarchicalBlockIdentifier>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<HierarchicalTfIdentifier>>::type v4;
public:
	HierarchicalBtfIdentifier() { }
	boost::make_variant_over<v4>::type choice;
};

class HierarchicalEventIdentifier
{
public:
	HierarchicalEventIdentifier() { }
	HierarchicalEventIdentifier(HierarchicalIdentifier * _hierarchicalIdentifier) { hierarchicalIdentifier = _hierarchicalIdentifier; }

	HierarchicalIdentifier *hierarchicalIdentifier;
};
class HierarchicalIdentifier
{
public:
	HierarchicalIdentifier() { }
	HierarchicalIdentifier(std::optional<int> * _discard, std::vector<std::tuple<Identifier, ConstantBitSelect>> * _identifier1, Identifier * _identifier2) { discard = _discard; identifier1 = _identifier1; identifier2 = _identifier2; }

	std::optional<int> *discard;
	std::vector<std::tuple<Identifier, ConstantBitSelect>> *identifier1;
	Identifier *identifier2;
};

class HierarchicalInstance
{
public:
	HierarchicalInstance() { }
	HierarchicalInstance(NameOfInstance * _nameOfInstance, std::optional<ListOfPortConnections> * _listOfPortConnections) { nameOfInstance = _nameOfInstance; listOfPortConnections = _listOfPortConnections; }

	NameOfInstance *nameOfInstance;
	std::optional<ListOfPortConnections> *listOfPortConnections;
};

class HierarchicalNetIdentifier
{
public:
	HierarchicalNetIdentifier() { }
	HierarchicalNetIdentifier(HierarchicalIdentifier * _hierarchicalIdentifier) { hierarchicalIdentifier = _hierarchicalIdentifier; }

	HierarchicalIdentifier *hierarchicalIdentifier;
};
class HierarchicalParameterIdentifier
{
public:
	HierarchicalParameterIdentifier() { }
	HierarchicalParameterIdentifier(HierarchicalIdentifier * _hierarchicalIdentifier) { hierarchicalIdentifier = _hierarchicalIdentifier; }

	HierarchicalIdentifier *hierarchicalIdentifier;
};
class HierarchicalPropertyIdentifier
{
public:
	HierarchicalPropertyIdentifier() { }
	HierarchicalPropertyIdentifier(HierarchicalIdentifier * _hierarchicalIdentifier) { hierarchicalIdentifier = _hierarchicalIdentifier; }

	HierarchicalIdentifier *hierarchicalIdentifier;
};
class HierarchicalSequenceIdentifier
{
public:
	HierarchicalSequenceIdentifier() { }
	HierarchicalSequenceIdentifier(HierarchicalIdentifier * _hierarchicalIdentifier) { hierarchicalIdentifier = _hierarchicalIdentifier; }

	HierarchicalIdentifier *hierarchicalIdentifier;
};
class HierarchicalTaskIdentifier
{
public:
	HierarchicalTaskIdentifier() { }
	HierarchicalTaskIdentifier(HierarchicalIdentifier * _hierarchicalIdentifier) { hierarchicalIdentifier = _hierarchicalIdentifier; }

	HierarchicalIdentifier *hierarchicalIdentifier;
};
class HierarchicalTfIdentifier
{
public:
	HierarchicalTfIdentifier() { }
	HierarchicalTfIdentifier(HierarchicalIdentifier * _hierarchicalIdentifier) { hierarchicalIdentifier = _hierarchicalIdentifier; }

	HierarchicalIdentifier *hierarchicalIdentifier;
};
class HierarchicalVariableIdentifier
{
public:
	HierarchicalVariableIdentifier() { }
	HierarchicalVariableIdentifier(HierarchicalIdentifier * _hierarchicalIdentifier) { hierarchicalIdentifier = _hierarchicalIdentifier; }

	HierarchicalIdentifier *hierarchicalIdentifier;
};
class HoldTimingCheck
{
public:
	HoldTimingCheck() { }
	HoldTimingCheck(ReferenceEvent * _referenceEvent, DataEvent * _dataEvent, TimingCheckLimit * _timingCheckLimit, std::optional<std::optional<Notifier>> * _notifier) { referenceEvent = _referenceEvent; dataEvent = _dataEvent; timingCheckLimit = _timingCheckLimit; notifier = _notifier; }

	ReferenceEvent *referenceEvent;
	DataEvent *dataEvent;
	TimingCheckLimit *timingCheckLimit;
	std::optional<std::optional<Notifier>> *notifier;
};

typedef std::string Identifier;
class IdentifierList
{
public:
	IdentifierList() { }
	IdentifierList(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class IfGenerateConstruct
{
public:
	IfGenerateConstruct() { }
	IfGenerateConstruct(ConstantExpression * _constantExpression, GenerateBlock * _generateBlock1, std::optional<GenerateBlock> * _generateBlock2) { constantExpression = _constantExpression; generateBlock1 = _generateBlock1; generateBlock2 = _generateBlock2; }

	ConstantExpression *constantExpression;
	GenerateBlock *generateBlock1;
	std::optional<GenerateBlock> *generateBlock2;
};

class ImmediateAssertionStatement
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<DeferredImmediateAssertionStatement>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<SimpleImmediateAssertionStatement>>::type v2;
public:
	ImmediateAssertionStatement() { }
	boost::make_variant_over<v2>::type choice;
};

enum class ImplicitClassHandle
{
	Super, This
};

class ImplicitDataType
{
public:
	ImplicitDataType() { }
	ImplicitDataType(std::optional<Signing> * _signing, std::vector<PackedDimension> * _packedDimension) { signing = _signing; packedDimension = _packedDimension; }

	std::optional<Signing> *signing;
	std::vector<PackedDimension> *packedDimension;
};

enum class ImportExport
{
	Import, Export
};

class IncOrDecExpression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<VariableLvalue, std::vector<AttributeInstance>, IncOrDecOperator>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<IncOrDecOperator, std::vector<AttributeInstance>, VariableLvalue>>>::type v2;
public:
	IncOrDecExpression() { }
	boost::make_variant_over<v2>::type choice;
};

enum class IncOrDecOperator
{
	Increment, Decrement
};

class IncludeStatement
{
public:
	IncludeStatement() { }
	IncludeStatement(FilePathSpec * _filePathSpec) { filePathSpec = _filePathSpec; }

	FilePathSpec *filePathSpec;
};

class IndexVariableIdentifier
{
public:
	IndexVariableIdentifier() { }
	IndexVariableIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class IndexedRange
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<Expression, ConstantExpression>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<Expression, ConstantExpression>>>::type v2;
public:
	IndexedRange() { }
	boost::make_variant_over<v2>::type choice;
};

class InitVal
{
public:
	InitVal() { }
	InitVal(Number * _number) { number = _number; }

	Number *number;
};
class InitialConstruct
{
public:
	InitialConstruct() { }
	InitialConstruct(StatementOrNull * _statementOrNull) { statementOrNull = _statementOrNull; }

	StatementOrNull *statementOrNull;
};

class InoutDeclaration
{
public:
	InoutDeclaration() { }
	InoutDeclaration(NetPortType * _netPortType, ListOfPortIdentifiers * _listOfPortIdentifiers) { netPortType = _netPortType; listOfPortIdentifiers = _listOfPortIdentifiers; }

	NetPortType *netPortType;
	ListOfPortIdentifiers *listOfPortIdentifiers;
};

class InoutPortIdentifier
{
public:
	InoutPortIdentifier() { }
	InoutPortIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class InoutTerminal
{
public:
	InoutTerminal() { }
	InoutTerminal(NetLvalue * _netLvalue) { netLvalue = _netLvalue; }

	NetLvalue *netLvalue;
};
class InputDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<VariablePortType, ListOfPortIdentifiers>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<NetPortType, ListOfPortIdentifiers>>>::type v2;
public:
	InputDeclaration() { }
	boost::make_variant_over<v2>::type choice;
};

class InputIdentifier
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<InterfaceIdentifier, PortIdentifier>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<InoutPortIdentifier>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<InputPortIdentifier>>::type v3;
public:
	InputIdentifier() { }
	boost::make_variant_over<v3>::type choice;
};

class InputPortIdentifier
{
public:
	InputPortIdentifier() { }
	InputPortIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class InputTerminal
{
public:
	InputTerminal() { }
	InputTerminal(Expression * _expression) { expression = _expression; }

	Expression *expression;
};
class InsideExpression
{
public:
	InsideExpression() { }
	InsideExpression(Expression * _expression, OpenRangeList * _openRangeList) { expression = _expression; openRangeList = _openRangeList; }

	Expression *expression;
	OpenRangeList *openRangeList;
};

class InstClause
{
public:
	InstClause() { }
	InstClause(InstName * _instName) { instName = _instName; }

	InstName *instName;
};

class InstName
{
public:
	InstName() { }
	InstName(TopmoduleIdentifier * _topmoduleIdentifier, std::vector<InstanceIdentifier> * _instanceIdentifier) { topmoduleIdentifier = _topmoduleIdentifier; instanceIdentifier = _instanceIdentifier; }

	TopmoduleIdentifier *topmoduleIdentifier;
	std::vector<InstanceIdentifier> *instanceIdentifier;
};

class InstanceIdentifier
{
public:
	InstanceIdentifier() { }
	InstanceIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
enum class IntegerAtomType
{
	Byte, Shortint, Int, Longint, Integer, Time
};

class IntegerCovergroupExpression
{
public:
	IntegerCovergroupExpression() { }
	IntegerCovergroupExpression(CovergroupExpression * _covergroupExpression) { covergroupExpression = _covergroupExpression; }

	CovergroupExpression *covergroupExpression;
};
class IntegerType
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<IntegerAtomType>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<IntegerVectorType>>::type v2;
public:
	IntegerType() { }
	boost::make_variant_over<v2>::type choice;
};

enum class IntegerVectorType
{
	Bit, Logic, Reg
};

class IntegralNumber
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<HexNumber>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<BinaryNumber>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<OctalNumber>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<DecimalNumber>>::type v4;
public:
	IntegralNumber() { }
	boost::make_variant_over<v4>::type choice;
};

class InterfaceAnsiHeader
{
public:
	InterfaceAnsiHeader() { }
	InterfaceAnsiHeader(std::vector<AttributeInstance> * _attributeInstance, std::optional<Lifetime> * _lifetime, InterfaceIdentifier * _interfaceIdentifier, std::vector<PackageImportDeclaration> * _packageImportDeclaration, std::optional<ParameterPortList> * _parameterPortList, std::optional<ListOfPortDeclarations> * _listOfPortDeclarations) { attributeInstance = _attributeInstance; lifetime = _lifetime; interfaceIdentifier = _interfaceIdentifier; packageImportDeclaration = _packageImportDeclaration; parameterPortList = _parameterPortList; listOfPortDeclarations = _listOfPortDeclarations; }

	std::vector<AttributeInstance> *attributeInstance;
	std::optional<Lifetime> *lifetime;
	InterfaceIdentifier *interfaceIdentifier;
	std::vector<PackageImportDeclaration> *packageImportDeclaration;
	std::optional<ParameterPortList> *parameterPortList;
	std::optional<ListOfPortDeclarations> *listOfPortDeclarations;
};

class InterfaceClassType
{
public:
	InterfaceClassType() { }
	InterfaceClassType(PsClassIdentifier * _psClassIdentifier, std::optional<ParameterValueAssignment> * _parameterValueAssignment) { psClassIdentifier = _psClassIdentifier; parameterValueAssignment = _parameterValueAssignment; }

	PsClassIdentifier *psClassIdentifier;
	std::optional<ParameterValueAssignment> *parameterValueAssignment;
};

class InterfaceDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<InterfaceAnsiHeader>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<InterfaceNonAnsiHeader>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, InterfaceIdentifier, std::optional<TimeunitsDeclaration>, std::vector<InterfaceItem>, std::optional<InterfaceIdentifier>>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<InterfaceAnsiHeader, std::optional<TimeunitsDeclaration>, std::vector<NonPortInterfaceItem>, std::optional<InterfaceIdentifier>>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<InterfaceNonAnsiHeader, std::optional<TimeunitsDeclaration>, std::vector<InterfaceItem>, std::optional<InterfaceIdentifier>>>>::type v5;
public:
	InterfaceDeclaration() { }
	boost::make_variant_over<v5>::type choice;
};

class InterfaceIdentifier
{
public:
	InterfaceIdentifier() { }
	InterfaceIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class InterfaceInstantiation
{
public:
	InterfaceInstantiation() { }
	InterfaceInstantiation(InterfaceIdentifier * _interfaceIdentifier, std::optional<ParameterValueAssignment> * _parameterValueAssignment, std::vector<HierarchicalInstance> * _hierarchicalInstance) { interfaceIdentifier = _interfaceIdentifier; parameterValueAssignment = _parameterValueAssignment; hierarchicalInstance = _hierarchicalInstance; }

	InterfaceIdentifier *interfaceIdentifier;
	std::optional<ParameterValueAssignment> *parameterValueAssignment;
	std::vector<HierarchicalInstance> *hierarchicalInstance;
};

class InterfaceIntanceIdentifier
{
public:
	InterfaceIntanceIdentifier() { }
	InterfaceIntanceIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class InterfaceItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<NonPortInterfaceItem>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<PortDeclaration>>::type v2;
public:
	InterfaceItem() { }
	boost::make_variant_over<v2>::type choice;
};

class InterfaceNonAnsiHeader
{
public:
	InterfaceNonAnsiHeader() { }
	InterfaceNonAnsiHeader(std::vector<AttributeInstance> * _attributeInstance, std::optional<Lifetime> * _lifetime, InterfaceIdentifier * _interfaceIdentifier, std::vector<PackageImportDeclaration> * _packageImportDeclaration, std::optional<ParameterPortList> * _parameterPortList, ListOfPorts * _listOfPorts) { attributeInstance = _attributeInstance; lifetime = _lifetime; interfaceIdentifier = _interfaceIdentifier; packageImportDeclaration = _packageImportDeclaration; parameterPortList = _parameterPortList; listOfPorts = _listOfPorts; }

	std::vector<AttributeInstance> *attributeInstance;
	std::optional<Lifetime> *lifetime;
	InterfaceIdentifier *interfaceIdentifier;
	std::vector<PackageImportDeclaration> *packageImportDeclaration;
	std::optional<ParameterPortList> *parameterPortList;
	ListOfPorts *listOfPorts;
};

class InterfaceOrGenerateItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ExternTfDeclaration>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ModportDeclaration>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ModuleCommonItem>>>::type v3;
public:
	InterfaceOrGenerateItem() { }
	boost::make_variant_over<v3>::type choice;
};

class InterfacePortDeclaration
{
public:
	InterfacePortDeclaration() { }
	InterfacePortDeclaration(InterfaceIdentifier * _interfaceIdentifier, std::optional<ModportIdentifier> * _modportIdentifier, ListOfInterfaceIdentifiers * _listOfInterfaceIdentifiers) { interfaceIdentifier = _interfaceIdentifier; modportIdentifier = _modportIdentifier; listOfInterfaceIdentifiers = _listOfInterfaceIdentifiers; }

	InterfaceIdentifier *interfaceIdentifier;
	std::optional<ModportIdentifier> *modportIdentifier;
	ListOfInterfaceIdentifiers *listOfInterfaceIdentifiers;
};

class InterfacePortHeader
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<InterfaceIdentifier, std::optional<ModportIdentifier>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::optional<ModportIdentifier>>>::type v2;
public:
	InterfacePortHeader() { }
	boost::make_variant_over<v2>::type choice;
};

enum class JoinKeyword
{
	Join, Joinany, Joinnone
};

class JumpStatement
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::optional<Expression>>>::type v1;
public:
	JumpStatement() { }
	boost::make_variant_over<v1>::type choice;
};

class LetActualArg
{
public:
	LetActualArg() { }
	LetActualArg(Expression * _expression) { expression = _expression; }

	Expression *expression;
};
class LetDeclaration
{
public:
	LetDeclaration() { }
	LetDeclaration(LetIdentifier * _letIdentifier, std::optional<std::optional<LetPortList>> * _letPortList, Expression * _expression) { letIdentifier = _letIdentifier; letPortList = _letPortList; expression = _expression; }

	LetIdentifier *letIdentifier;
	std::optional<std::optional<LetPortList>> *letPortList;
	Expression *expression;
};

class LetExpression
{
public:
	LetExpression() { }
	LetExpression(std::optional<PackageScope> * _packageScope, LetIdentifier * _letIdentifier, std::optional<std::optional<LetListOfArguments>> * _letListOfArguments) { packageScope = _packageScope; letIdentifier = _letIdentifier; letListOfArguments = _letListOfArguments; }

	std::optional<PackageScope> *packageScope;
	LetIdentifier *letIdentifier;
	std::optional<std::optional<LetListOfArguments>> *letListOfArguments;
};

class LetFormalType
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<DataTypeOrImplicit>>::type v1;
public:
	LetFormalType() { }
	boost::make_variant_over<v1>::type choice;
};

class LetIdentifier
{
public:
	LetIdentifier() { }
	LetIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class LetListOfArguments
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::vector<std::tuple<Identifier, std::optional<LetActualArg>>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<std::optional<LetActualArg>>, std::optional<std::vector<std::tuple<Identifier, std::optional<LetActualArg>>>>>>>::type v2;
public:
	LetListOfArguments() { }
	boost::make_variant_over<v2>::type choice;
};

class LetPortItem
{
public:
	LetPortItem() { }
	LetPortItem(std::vector<AttributeInstance> * _attributeInstance, LetFormalType * _letFormalType, FormalPortIdentifier * _formalPortIdentifier, std::vector<VariableDimension> * _variableDimension, std::optional<Expression> * _expression) { attributeInstance = _attributeInstance; letFormalType = _letFormalType; formalPortIdentifier = _formalPortIdentifier; variableDimension = _variableDimension; expression = _expression; }

	std::vector<AttributeInstance> *attributeInstance;
	LetFormalType *letFormalType;
	FormalPortIdentifier *formalPortIdentifier;
	std::vector<VariableDimension> *variableDimension;
	std::optional<Expression> *expression;
};

class LetPortList
{
public:
	LetPortList() { }
	LetPortList(LetPortItem * _letPortItem) { letPortItem = _letPortItem; }

	LetPortItem *letPortItem;
};
class LevelInputList
{
public:
	LevelInputList() { }
	LevelInputList(LevelSymbol * _levelSymbol) { levelSymbol = _levelSymbol; }

	LevelSymbol *levelSymbol;
};
class LevelSymbol
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<Identifier>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<Number>>::type v2;
public:
	LevelSymbol() { }
	boost::make_variant_over<v2>::type choice;
};

class LiblistClause
{
public:
	LiblistClause() { }
	LiblistClause(std::vector<LibraryIdentifier> * _libraryIdentifier) { libraryIdentifier = _libraryIdentifier; }

	std::vector<LibraryIdentifier> *libraryIdentifier;
};

class LibraryDeclaration
{
public:
	LibraryDeclaration() { }
	LibraryDeclaration(LibraryIdentifier * _libraryIdentifier, std::vector<FilePathSpec> * _filePathSpec1, std::optional<std::vector<FilePathSpec>> * _filePathSpec2) { libraryIdentifier = _libraryIdentifier; filePathSpec1 = _filePathSpec1; filePathSpec2 = _filePathSpec2; }

	LibraryIdentifier *libraryIdentifier;
	std::vector<FilePathSpec> *filePathSpec1;
	std::optional<std::vector<FilePathSpec>> *filePathSpec2;
};

class LibraryDescription
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ConfigDeclaration>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<IncludeStatement>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<LibraryDeclaration>>::type v3;
public:
	LibraryDescription() { }
	boost::make_variant_over<v3>::type choice;
};

class LibraryIdentifier
{
public:
	LibraryIdentifier() { }
	LibraryIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class LibraryText
{
public:
	LibraryText() { }
	LibraryText(LibraryDescription * _libraryDescription) { libraryDescription = _libraryDescription; }

	LibraryDescription *libraryDescription;
};
enum class Lifetime
{
	Static, Automatic
};

class LimitValue
{
public:
	LimitValue() { }
	LimitValue(ConstantMintypmaxExpression * _constantMintypmaxExpression) { constantMintypmaxExpression = _constantMintypmaxExpression; }

	ConstantMintypmaxExpression *constantMintypmaxExpression;
};
class ListOfArguments
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::vector<std::tuple<Identifier, std::optional<Expression>>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<std::optional<Expression>>, std::vector<std::tuple<Identifier, std::optional<Expression>>>>>>::type v2;
public:
	ListOfArguments() { }
	boost::make_variant_over<v2>::type choice;
};

class ListOfCheckerPortConnections
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::vector<NamedCheckerPortConnection>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::vector<OrderedCheckerPortConnection>>>::type v2;
public:
	ListOfCheckerPortConnections() { }
	boost::make_variant_over<v2>::type choice;
};

class ListOfClockingDeclAssign
{
public:
	ListOfClockingDeclAssign() { }
	ListOfClockingDeclAssign(ClockingDeclAssign * _clockingDeclAssign) { clockingDeclAssign = _clockingDeclAssign; }

	ClockingDeclAssign *clockingDeclAssign;
};
class ListOfCrossItems
{
public:
	ListOfCrossItems() { }
	ListOfCrossItems(CrossItem * _crossItem0, std::vector<CrossItem> * _crossItem1) { crossItem0 = _crossItem0; crossItem1 = _crossItem1; }

	CrossItem *crossItem0;
	std::vector<CrossItem> *crossItem1;
};

class ListOfDefparamAssignments
{
public:
	ListOfDefparamAssignments() { }
	ListOfDefparamAssignments(DefparamAssignment * _defparamAssignment) { defparamAssignment = _defparamAssignment; }

	DefparamAssignment *defparamAssignment;
};
class ListOfGenvarIdentifiers
{
public:
	ListOfGenvarIdentifiers() { }
	ListOfGenvarIdentifiers(GenvarIdentifier * _genvarIdentifier) { genvarIdentifier = _genvarIdentifier; }

	GenvarIdentifier *genvarIdentifier;
};
class ListOfInterfaceIdentifiers
{
public:
	ListOfInterfaceIdentifiers() { }
	ListOfInterfaceIdentifiers(std::tuple<InterfaceIdentifier, std::vector<UnpackedDimension>> * _interfaceIdentifier) { interfaceIdentifier = _interfaceIdentifier; }

	std::tuple<InterfaceIdentifier, std::vector<UnpackedDimension>> *interfaceIdentifier;
};
class ListOfNetAssignments
{
public:
	ListOfNetAssignments() { }
	ListOfNetAssignments(NetAssignment * _netAssignment) { netAssignment = _netAssignment; }

	NetAssignment *netAssignment;
};
class ListOfNetDeclAssignments
{
public:
	ListOfNetDeclAssignments() { }
	ListOfNetDeclAssignments(NetDeclAssignment * _netDeclAssignment) { netDeclAssignment = _netDeclAssignment; }

	NetDeclAssignment *netDeclAssignment;
};
class ListOfParamAssignments
{
public:
	ListOfParamAssignments() { }
	ListOfParamAssignments(ParamAssignment * _paramAssignment) { paramAssignment = _paramAssignment; }

	ParamAssignment *paramAssignment;
};
class ListOfParameterAssignments
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::vector<NamedParameterAssignment>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::vector<OrderedParameterAssignment>>>::type v2;
public:
	ListOfParameterAssignments() { }
	boost::make_variant_over<v2>::type choice;
};

class ListOfPathDelayExpressions
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<T01PathDelayExpression, T10PathDelayExpression, T0zPathDelayExpression, Tz1PathDelayExpression, T1zPathDelayExpression, Tz0PathDelayExpression, T0xPathDelayExpression, Tx1PathDelayExpression, T1xPathDelayExpression, Tx0PathDelayExpression, TxzPathDelayExpression, TzxPathDelayExpression>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<T01PathDelayExpression, T10PathDelayExpression, T0zPathDelayExpression, Tz1PathDelayExpression, T1zPathDelayExpression, Tz0PathDelayExpression>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<TrisePathDelayExpression, TfallPathDelayExpression, TzPathDelayExpression>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<TrisePathDelayExpression, TfallPathDelayExpression>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<TPathDelayExpression>>::type v5;
public:
	ListOfPathDelayExpressions() { }
	boost::make_variant_over<v5>::type choice;
};

class ListOfPathInputs
{
public:
	ListOfPathInputs() { }
	ListOfPathInputs(SpecifyInputTerminalDescriptor * _specifyInputTerminalDescriptor) { specifyInputTerminalDescriptor = _specifyInputTerminalDescriptor; }

	SpecifyInputTerminalDescriptor *specifyInputTerminalDescriptor;
};
class ListOfPathOutputs
{
public:
	ListOfPathOutputs() { }
	ListOfPathOutputs(SpecifyOutputTerminalDescriptor * _specifyOutputTerminalDescriptor) { specifyOutputTerminalDescriptor = _specifyOutputTerminalDescriptor; }

	SpecifyOutputTerminalDescriptor *specifyOutputTerminalDescriptor;
};
class ListOfPortConnections
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::vector<NamedPortConnection>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::vector<OrderedPortConnection>>>::type v2;
public:
	ListOfPortConnections() { }
	boost::make_variant_over<v2>::type choice;
};

class ListOfPortDeclarations
{
public:
	ListOfPortDeclarations() { }
	ListOfPortDeclarations(std::optional<std::vector<std::tuple<std::vector<AttributeInstance>, AnsiPortDeclaration>>> * _attributeInstance) { attributeInstance = _attributeInstance; }

	std::optional<std::vector<std::tuple<std::vector<AttributeInstance>, AnsiPortDeclaration>>> *attributeInstance;
};

class ListOfPortIdentifiers
{
public:
	ListOfPortIdentifiers() { }
	ListOfPortIdentifiers(std::tuple<PortIdentifier, std::vector<UnpackedDimension>> * _portIdentifier) { portIdentifier = _portIdentifier; }

	std::tuple<PortIdentifier, std::vector<UnpackedDimension>> *portIdentifier;
};
class ListOfPorts
{
public:
	ListOfPorts() { }
	ListOfPorts(std::vector<Port> * _port) { port = _port; }

	std::vector<Port> *port;
};

class ListOfSpecparamAssignments
{
public:
	ListOfSpecparamAssignments() { }
	ListOfSpecparamAssignments(SpecparamAssignment * _specparamAssignment) { specparamAssignment = _specparamAssignment; }

	SpecparamAssignment *specparamAssignment;
};
class ListOfTfVariableIdentifiers
{
public:
	ListOfTfVariableIdentifiers() { }
	ListOfTfVariableIdentifiers(std::tuple<PortIdentifier, std::vector<VariableDimension>, std::optional<Expression>> * _portIdentifier) { portIdentifier = _portIdentifier; }

	std::tuple<PortIdentifier, std::vector<VariableDimension>, std::optional<Expression>> *portIdentifier;
};
class ListOfTypeAssignments
{
public:
	ListOfTypeAssignments() { }
	ListOfTypeAssignments(TypeAssignment * _typeAssignment) { typeAssignment = _typeAssignment; }

	TypeAssignment *typeAssignment;
};
class ListOfUdpPortIdentifiers
{
public:
	ListOfUdpPortIdentifiers() { }
	ListOfUdpPortIdentifiers(PortIdentifier * _portIdentifier) { portIdentifier = _portIdentifier; }

	PortIdentifier *portIdentifier;
};
class ListOfVariableAssignments
{
public:
	ListOfVariableAssignments() { }
	ListOfVariableAssignments(VariableAssignment * _variableAssignment) { variableAssignment = _variableAssignment; }

	VariableAssignment *variableAssignment;
};
class ListOfVariableDeclAssignments
{
public:
	ListOfVariableDeclAssignments() { }
	ListOfVariableDeclAssignments(VariableDeclAssignment * _variableDeclAssignment) { variableDeclAssignment = _variableDeclAssignment; }

	VariableDeclAssignment *variableDeclAssignment;
};
class ListOfVariableIdentifiers
{
public:
	ListOfVariableIdentifiers() { }
	ListOfVariableIdentifiers(std::tuple<VariableIdentifier, std::vector<VariableDimension>> * _variableIdentifier) { variableIdentifier = _variableIdentifier; }

	std::tuple<VariableIdentifier, std::vector<VariableDimension>> *variableIdentifier;
};
class LocalParameterDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ListOfTypeAssignments>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<DataTypeOrImplicit, ListOfParamAssignments>>>::type v2;
public:
	LocalParameterDeclaration() { }
	boost::make_variant_over<v2>::type choice;
};

class LoopGenerateConstruct
{
public:
	LoopGenerateConstruct() { }
	LoopGenerateConstruct(GenvarInitialization * _genvarInitialization, GenvarExpression * _genvarExpression, GenvarIteration * _genvarIteration, GenerateBlock * _generateBlock) { genvarInitialization = _genvarInitialization; genvarExpression = _genvarExpression; genvarIteration = _genvarIteration; generateBlock = _generateBlock; }

	GenvarInitialization *genvarInitialization;
	GenvarExpression *genvarExpression;
	GenvarIteration *genvarIteration;
	GenerateBlock *generateBlock;
};

class LoopStatement
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<PsOrHierarchicalArrayIdentifier, LoopVariables, Statement>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<StatementOrNull, Expression>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::optional<ForInitialization>, std::optional<Expression>, std::optional<ForStep>, StatementOrNull>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<Expression, StatementOrNull>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<Expression, StatementOrNull>>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<StatementOrNull>>::type v6;
public:
	LoopStatement() { }
	boost::make_variant_over<v6>::type choice;
};

class LoopVariables
{
public:
	LoopVariables() { }
	LoopVariables(std::optional<IndexVariableIdentifier> * _indexVariableIdentifier) { indexVariableIdentifier = _indexVariableIdentifier; }

	std::optional<IndexVariableIdentifier> *indexVariableIdentifier;
};
class MemberIdentifier
{
public:
	MemberIdentifier() { }
	MemberIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class MethodCall
{
public:
	MethodCall() { }
	MethodCall(MethodCallRoot * _methodCallRoot, MethodCallBody * _methodCallBody) { methodCallRoot = _methodCallRoot; methodCallBody = _methodCallBody; }

	MethodCallRoot *methodCallRoot;
	MethodCallBody *methodCallBody;
};

class MethodCallBody
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<BuiltInMethodCall>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<MethodIdentifier, std::vector<AttributeInstance>, std::optional<ListOfArguments>>>>::type v2;
public:
	MethodCallBody() { }
	boost::make_variant_over<v2>::type choice;
};

class MethodCallRoot
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ImplicitClassHandle>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<Primary>>::type v2;
public:
	MethodCallRoot() { }
	boost::make_variant_over<v2>::type choice;
};

class MethodIdentifier
{
public:
	MethodIdentifier() { }
	MethodIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class MethodPrototype
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<FunctionPrototype>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<TaskPrototype>>::type v2;
public:
	MethodPrototype() { }
	boost::make_variant_over<v2>::type choice;
};

class MethodQualifier
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ClassItemQualifier>>::type v1;
public:
	MethodQualifier() { }
	boost::make_variant_over<v1>::type choice;
};

class MintypmaxExpression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<Expression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<Expression, Expression, Expression>>>::type v2;
public:
	MintypmaxExpression() { }
	boost::make_variant_over<v2>::type choice;
};

class ModportClockingDeclaration
{
public:
	ModportClockingDeclaration() { }
	ModportClockingDeclaration(ClockingIdentifier * _clockingIdentifier) { clockingIdentifier = _clockingIdentifier; }

	ClockingIdentifier *clockingIdentifier;
};

class ModportDeclaration
{
public:
	ModportDeclaration() { }
	ModportDeclaration(std::vector<ModportItem> * _modportItem) { modportItem = _modportItem; }

	std::vector<ModportItem> *modportItem;
};

class ModportIdentifier
{
public:
	ModportIdentifier() { }
	ModportIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class ModportItem
{
public:
	ModportItem() { }
	ModportItem(ModportIdentifier * _modportIdentifier, std::vector<ModportPortsDeclaration> * _modportPortsDeclaration) { modportIdentifier = _modportIdentifier; modportPortsDeclaration = _modportPortsDeclaration; }

	ModportIdentifier *modportIdentifier;
	std::vector<ModportPortsDeclaration> *modportPortsDeclaration;
};

class ModportPortsDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ModportClockingDeclaration>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ModportTfPortsDeclaration>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ModportSimplePortsDeclaration>>>::type v3;
public:
	ModportPortsDeclaration() { }
	boost::make_variant_over<v3>::type choice;
};

class ModportSimplePort
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<PortIdentifier, std::optional<Expression>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<PortIdentifier>>::type v2;
public:
	ModportSimplePort() { }
	boost::make_variant_over<v2>::type choice;
};

class ModportSimplePortsDeclaration
{
public:
	ModportSimplePortsDeclaration() { }
	ModportSimplePortsDeclaration(PortDirection * _portDirection, std::vector<ModportSimplePort> * _modportSimplePort) { portDirection = _portDirection; modportSimplePort = _modportSimplePort; }

	PortDirection *portDirection;
	std::vector<ModportSimplePort> *modportSimplePort;
};

class ModportTfPort
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<TfIdentifier>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<MethodPrototype>>::type v2;
public:
	ModportTfPort() { }
	boost::make_variant_over<v2>::type choice;
};

class ModportTfPortsDeclaration
{
public:
	ModportTfPortsDeclaration() { }
	ModportTfPortsDeclaration(ImportExport * _importExport, std::vector<ModportTfPort> * _modportTfPort) { importExport = _importExport; modportTfPort = _modportTfPort; }

	ImportExport *importExport;
	std::vector<ModportTfPort> *modportTfPort;
};

class ModuleAnsiHeader
{
public:
	ModuleAnsiHeader() { }
	ModuleAnsiHeader(std::vector<AttributeInstance> * _attributeInstance, ModuleKeyword * _moduleKeyword, std::optional<Lifetime> * _lifetime, ModuleIdentifier * _moduleIdentifier, std::vector<PackageImportDeclaration> * _packageImportDeclaration, std::optional<ParameterPortList> * _parameterPortList, std::optional<ListOfPortDeclarations> * _listOfPortDeclarations) { attributeInstance = _attributeInstance; moduleKeyword = _moduleKeyword; lifetime = _lifetime; moduleIdentifier = _moduleIdentifier; packageImportDeclaration = _packageImportDeclaration; parameterPortList = _parameterPortList; listOfPortDeclarations = _listOfPortDeclarations; }

	std::vector<AttributeInstance> *attributeInstance;
	ModuleKeyword *moduleKeyword;
	std::optional<Lifetime> *lifetime;
	ModuleIdentifier *moduleIdentifier;
	std::vector<PackageImportDeclaration> *packageImportDeclaration;
	std::optional<ParameterPortList> *parameterPortList;
	std::optional<ListOfPortDeclarations> *listOfPortDeclarations;
};

class ModuleCommonItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ElaborationSystemTask>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ConditionalGenerateConstruct>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<LoopGenerateConstruct>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<AlwaysConstruct>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<FinalConstruct>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<InitialConstruct>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<NetAlias>>::type v7;
	typedef boost::mpl::push_front<v7, boost::recursive_wrapper<ContinuousAssign>>::type v8;
	typedef boost::mpl::push_front<v8, boost::recursive_wrapper<BindDirective>>::type v9;
	typedef boost::mpl::push_front<v9, boost::recursive_wrapper<AssertionItem>>::type v10;
	typedef boost::mpl::push_front<v10, boost::recursive_wrapper<ProgramInstantiation>>::type v11;
	typedef boost::mpl::push_front<v11, boost::recursive_wrapper<InterfaceInstantiation>>::type v12;
	typedef boost::mpl::push_front<v12, boost::recursive_wrapper<ModuleOrGenerateItemDeclaration>>::type v13;
public:
	ModuleCommonItem() { }
	boost::make_variant_over<v13>::type choice;
};

class ModuleDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ModuleAnsiHeader>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ModuleNonAnsiHeader>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ModuleKeyword, std::optional<Lifetime>, ModuleIdentifier, std::optional<TimeunitsDeclaration>, std::vector<ModuleItem>, std::optional<ModuleIdentifier>>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<ModuleAnsiHeader, std::optional<TimeunitsDeclaration>, std::vector<NonPortModuleItem>, std::optional<ModuleIdentifier>>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<ModuleNonAnsiHeader, std::optional<TimeunitsDeclaration>, std::vector<ModuleItem>, std::optional<ModuleIdentifier>>>>::type v5;
public:
	ModuleDeclaration() { }
	boost::make_variant_over<v5>::type choice;
};

class ModuleIdentifier
{
public:
	ModuleIdentifier() { }
	ModuleIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class ModuleInstantiation
{
public:
	ModuleInstantiation() { }
	ModuleInstantiation(ModuleIdentifier * _moduleIdentifier, std::optional<ParameterValueAssignment> * _parameterValueAssignment, std::vector<HierarchicalInstance> * _hierarchicalInstance) { moduleIdentifier = _moduleIdentifier; parameterValueAssignment = _parameterValueAssignment; hierarchicalInstance = _hierarchicalInstance; }

	ModuleIdentifier *moduleIdentifier;
	std::optional<ParameterValueAssignment> *parameterValueAssignment;
	std::vector<HierarchicalInstance> *hierarchicalInstance;
};

class ModuleItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<NonPortModuleItem>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<PortDeclaration>>::type v2;
public:
	ModuleItem() { }
	boost::make_variant_over<v2>::type choice;
};

enum class ModuleKeyword
{
	Module, Macromodule
};

class ModuleNonAnsiHeader
{
public:
	ModuleNonAnsiHeader() { }
	ModuleNonAnsiHeader(std::vector<AttributeInstance> * _attributeInstance, ModuleKeyword * _moduleKeyword, std::optional<Lifetime> * _lifetime, ModuleIdentifier * _moduleIdentifier, std::vector<PackageImportDeclaration> * _packageImportDeclaration, std::optional<ParameterPortList> * _parameterPortList, ListOfPorts * _listOfPorts) { attributeInstance = _attributeInstance; moduleKeyword = _moduleKeyword; lifetime = _lifetime; moduleIdentifier = _moduleIdentifier; packageImportDeclaration = _packageImportDeclaration; parameterPortList = _parameterPortList; listOfPorts = _listOfPorts; }

	std::vector<AttributeInstance> *attributeInstance;
	ModuleKeyword *moduleKeyword;
	std::optional<Lifetime> *lifetime;
	ModuleIdentifier *moduleIdentifier;
	std::vector<PackageImportDeclaration> *packageImportDeclaration;
	std::optional<ParameterPortList> *parameterPortList;
	ListOfPorts *listOfPorts;
};

class ModuleOrGenerateItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ModuleCommonItem>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ModuleInstantiation>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, UdpInstantiation>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, GateInstantiation>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ParameterOverride>>>::type v5;
public:
	ModuleOrGenerateItem() { }
	boost::make_variant_over<v5>::type choice;
};

class ModuleOrGenerateItemDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ExpressionOrDist>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ModuleIdentifier>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<ClockingDeclaration>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<GenvarDeclaration>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<PackageOrGenerateItemDeclaration>>::type v5;
public:
	ModuleOrGenerateItemDeclaration() { }
	boost::make_variant_over<v5>::type choice;
};

class ModulePathConcatenation
{
public:
	ModulePathConcatenation() { }
	ModulePathConcatenation(std::vector<ModulePathExpression> * _modulePathExpression) { modulePathExpression = _modulePathExpression; }

	std::vector<ModulePathExpression> *modulePathExpression;
};

class ModulePathConditionalExpression
{
public:
	ModulePathConditionalExpression() { }
	ModulePathConditionalExpression(ModulePathExpression * _modulePathExpression0, std::vector<AttributeInstance> * _attributeInstance, ModulePathExpression * _modulePathExpression2, ModulePathExpression * _modulePathExpression3) { modulePathExpression0 = _modulePathExpression0; attributeInstance = _attributeInstance; modulePathExpression2 = _modulePathExpression2; modulePathExpression3 = _modulePathExpression3; }

	ModulePathExpression *modulePathExpression0;
	std::vector<AttributeInstance> *attributeInstance;
	ModulePathExpression *modulePathExpression2;
	ModulePathExpression *modulePathExpression3;
};

class ModulePathExpression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ModulePathConditionalExpression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<ModulePathExpression, BinaryModulePathOperator, std::vector<AttributeInstance>, ModulePathExpression>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<UnaryModulePathOperator, std::vector<AttributeInstance>, ModulePathPrimary>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<ModulePathPrimary>>::type v4;
public:
	ModulePathExpression() { }
	boost::make_variant_over<v4>::type choice;
};

class ModulePathMintypmaxExpression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ModulePathExpression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<ModulePathExpression, ModulePathExpression, ModulePathExpression>>>::type v2;
public:
	ModulePathMintypmaxExpression() { }
	boost::make_variant_over<v2>::type choice;
};

class ModulePathMultipleConcatenation
{
public:
	ModulePathMultipleConcatenation() { }
	ModulePathMultipleConcatenation(ConstantExpression * _constantExpression, ModulePathConcatenation * _modulePathConcatenation) { constantExpression = _constantExpression; modulePathConcatenation = _modulePathConcatenation; }

	ConstantExpression *constantExpression;
	ModulePathConcatenation *modulePathConcatenation;
};

class ModulePathPrimary
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ModulePathMintypmaxExpression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<FunctionSubroutineCall>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<ModulePathMultipleConcatenation>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<ModulePathConcatenation>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<Identifier>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<Number>>::type v6;
public:
	ModulePathPrimary() { }
	boost::make_variant_over<v6>::type choice;
};

class MosSwitchInstance
{
public:
	MosSwitchInstance() { }
	MosSwitchInstance(std::optional<NameOfInstance> * _nameOfInstance, OutputTerminal * _outputTerminal, InputTerminal * _inputTerminal, EnableTerminal * _enableTerminal) { nameOfInstance = _nameOfInstance; outputTerminal = _outputTerminal; inputTerminal = _inputTerminal; enableTerminal = _enableTerminal; }

	std::optional<NameOfInstance> *nameOfInstance;
	OutputTerminal *outputTerminal;
	InputTerminal *inputTerminal;
	EnableTerminal *enableTerminal;
};

enum class MosSwitchtype
{
	Nmos, Pmos, Rnmos, Rpmos
};

class MultipleConcatenation
{
public:
	MultipleConcatenation() { }
	MultipleConcatenation(Expression * _expression, Concatenation * _concatenation) { expression = _expression; concatenation = _concatenation; }

	Expression *expression;
	Concatenation *concatenation;
};

class NControlTerminal
{
public:
	NControlTerminal() { }
	NControlTerminal(Expression * _expression) { expression = _expression; }

	Expression *expression;
};
class NInputGateInstance
{
public:
	NInputGateInstance() { }
	NInputGateInstance(std::optional<NameOfInstance> * _nameOfInstance, OutputTerminal * _outputTerminal, std::vector<InputTerminal> * _inputTerminal) { nameOfInstance = _nameOfInstance; outputTerminal = _outputTerminal; inputTerminal = _inputTerminal; }

	std::optional<NameOfInstance> *nameOfInstance;
	OutputTerminal *outputTerminal;
	std::vector<InputTerminal> *inputTerminal;
};

enum class NInputGatetype
{
	And, Nand, Or, Nor, Xor, Xnor
};

class NOutputGateInstance
{
public:
	NOutputGateInstance() { }
	NOutputGateInstance(std::optional<NameOfInstance> * _nameOfInstance, std::vector<OutputTerminal> * _outputTerminal, InputTerminal * _inputTerminal) { nameOfInstance = _nameOfInstance; outputTerminal = _outputTerminal; inputTerminal = _inputTerminal; }

	std::optional<NameOfInstance> *nameOfInstance;
	std::vector<OutputTerminal> *outputTerminal;
	InputTerminal *inputTerminal;
};

enum class NOutputGatetype
{
	Buf, Not
};

class NameOfInstance
{
public:
	NameOfInstance() { }
	NameOfInstance(InstanceIdentifier * _instanceIdentifier, std::vector<UnpackedDimension> * _unpackedDimension) { instanceIdentifier = _instanceIdentifier; unpackedDimension = _unpackedDimension; }

	InstanceIdentifier *instanceIdentifier;
	std::vector<UnpackedDimension> *unpackedDimension;
};

class NamedCheckerPortConnection
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, std::optional<std::optional<PropertyActualArg>>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, FormalPortIdentifier, std::optional<std::optional<PropertyActualArg>>>>>::type v2;
public:
	NamedCheckerPortConnection() { }
	boost::make_variant_over<v2>::type choice;
};

class NamedParameterAssignment
{
public:
	NamedParameterAssignment() { }
	NamedParameterAssignment(ParameterIdentifier * _parameterIdentifier, std::optional<ParamExpression> * _paramExpression) { parameterIdentifier = _parameterIdentifier; paramExpression = _paramExpression; }

	ParameterIdentifier *parameterIdentifier;
	std::optional<ParamExpression> *paramExpression;
};

class NamedPortConnection
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, std::optional<std::optional<Expression>>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, PortIdentifier, std::optional<std::optional<Expression>>>>>::type v2;
public:
	NamedPortConnection() { }
	boost::make_variant_over<v2>::type choice;
};

class NetAlias
{
public:
	NetAlias() { }
	NetAlias(NetLvalue * _netLvalue0, std::vector<NetLvalue> * _netLvalue1) { netLvalue0 = _netLvalue0; netLvalue1 = _netLvalue1; }

	NetLvalue *netLvalue0;
	std::vector<NetLvalue> *netLvalue1;
};

class NetAssignment
{
public:
	NetAssignment() { }
	NetAssignment(NetLvalue * _netLvalue, Expression * _expression) { netLvalue = _netLvalue; expression = _expression; }

	NetLvalue *netLvalue;
	Expression *expression;
};

class NetDeclAssignment
{
public:
	NetDeclAssignment() { }
	NetDeclAssignment(NetIdentifier * _netIdentifier, std::vector<UnpackedDimension> * _unpackedDimension, std::optional<Expression> * _expression) { netIdentifier = _netIdentifier; unpackedDimension = _unpackedDimension; expression = _expression; }

	NetIdentifier *netIdentifier;
	std::vector<UnpackedDimension> *unpackedDimension;
	std::optional<Expression> *expression;
};

class NetDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<ImplicitDataType, std::optional<DelayValue>, NetIdentifier, std::vector<UnpackedDimension>, std::optional<std::tuple<NetIdentifier, std::vector<UnpackedDimension>>>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<NetTypeIdentifier, std::optional<DelayControl>, ListOfNetDeclAssignments>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<NetType, std::optional<ChargeStrength>, DataTypeOrImplicit, std::optional<Delay3>, ListOfNetDeclAssignments>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<NetType, std::optional<ChargeStrength>, DataTypeOrImplicit, std::optional<Delay3>, ListOfNetDeclAssignments>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<NetType, std::optional<DriveStrength>, DataTypeOrImplicit, std::optional<Delay3>, ListOfNetDeclAssignments>>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<std::tuple<NetType, std::optional<DriveStrength>, DataTypeOrImplicit, std::optional<Delay3>, ListOfNetDeclAssignments>>>::type v6;
public:
	NetDeclaration() { }
	boost::make_variant_over<v6>::type choice;
};

class NetIdentifier
{
public:
	NetIdentifier() { }
	NetIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class NetLvalue
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<AssignmentPatternExpressionType>, AssignmentPatternNetLvalue>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::vector<NetLvalue>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<PsOrHierarchicalNetIdentifier, ConstantSelect>>>::type v3;
public:
	NetLvalue() { }
	boost::make_variant_over<v3>::type choice;
};

class NetPortHeader
{
public:
	NetPortHeader() { }
	NetPortHeader(std::optional<PortDirection> * _portDirection, NetPortType * _netPortType) { portDirection = _portDirection; netPortType = _netPortType; }

	std::optional<PortDirection> *portDirection;
	NetPortType *netPortType;
};

class NetPortType
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ImplicitDataType>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<NetTypeIdentifier>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::optional<NetType>, DataTypeOrImplicit>>>::type v3;
public:
	NetPortType() { }
	boost::make_variant_over<v3>::type choice;
};

enum class NetType
{
	Supply0, Supply1, Tri, Triand, Trior, Trireg, Tri0, Tri1, Uwire, Wire, Wand, Wor
};

class NetTypeDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<ClassScope>, NetTypeIdentifier, NetTypeIdentifier>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<PackageScope>, NetTypeIdentifier, NetTypeIdentifier>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<DataType, NetTypeIdentifier, std::optional<std::tuple<std::optional<ClassScope>, TfIdentifier>>>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<DataType, NetTypeIdentifier, std::optional<std::tuple<std::optional<PackageScope>, TfIdentifier>>>>>::type v4;
public:
	NetTypeDeclaration() { }
	boost::make_variant_over<v4>::type choice;
};

class NetTypeIdentifier
{
public:
	NetTypeIdentifier() { }
	NetTypeIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class NextState
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<OutputSymbol>>::type v1;
public:
	NextState() { }
	boost::make_variant_over<v1>::type choice;
};

class NochangeTimingCheck
{
public:
	NochangeTimingCheck() { }
	NochangeTimingCheck(ReferenceEvent * _referenceEvent, DataEvent * _dataEvent, StartEdgeOffset * _startEdgeOffset, EndEdgeOffset * _endEdgeOffset, std::optional<std::optional<Notifier>> * _notifier) { referenceEvent = _referenceEvent; dataEvent = _dataEvent; startEdgeOffset = _startEdgeOffset; endEdgeOffset = _endEdgeOffset; notifier = _notifier; }

	ReferenceEvent *referenceEvent;
	DataEvent *dataEvent;
	StartEdgeOffset *startEdgeOffset;
	EndEdgeOffset *endEdgeOffset;
	std::optional<std::optional<Notifier>> *notifier;
};

class NonConsecutiveRepetition
{
public:
	NonConsecutiveRepetition() { }
	NonConsecutiveRepetition(ConstOrRangeExpression * _constOrRangeExpression) { constOrRangeExpression = _constOrRangeExpression; }

	ConstOrRangeExpression *constOrRangeExpression;
};

enum class NonIntegerType
{
	Shortreal, Real, Realtime
};

class NonPortInterfaceItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<TimeunitsDeclaration>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<InterfaceDeclaration>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<ProgramDeclaration>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<InterfaceOrGenerateItem>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<GenerateRegion>>::type v5;
public:
	NonPortInterfaceItem() { }
	boost::make_variant_over<v5>::type choice;
};

class NonPortModuleItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<TimeunitsDeclaration>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<InterfaceDeclaration>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<ModuleDeclaration>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<ProgramDeclaration>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, SpecparamDeclaration>>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<SpecifyBlock>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<ModuleOrGenerateItem>>::type v7;
	typedef boost::mpl::push_front<v7, boost::recursive_wrapper<GenerateRegion>>::type v8;
public:
	NonPortModuleItem() { }
	boost::make_variant_over<v8>::type choice;
};

class NonPortProgramItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ProgramGenerateItem>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<TimeunitsDeclaration>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ConcurrentAssertionItem>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, FinalConstruct>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, InitialConstruct>>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ModuleOrGenerateItemDeclaration>>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ContinuousAssign>>>::type v7;
public:
	NonPortProgramItem() { }
	boost::make_variant_over<v7>::type choice;
};

class NonblockingAssignment
{
public:
	NonblockingAssignment() { }
	NonblockingAssignment(VariableLvalue * _variableLvalue, std::optional<DelayOrEventControl> * _delayOrEventControl, Expression * _expression) { variableLvalue = _variableLvalue; delayOrEventControl = _delayOrEventControl; expression = _expression; }

	VariableLvalue *variableLvalue;
	std::optional<DelayOrEventControl> *delayOrEventControl;
	Expression *expression;
};

class NonrangeSelect
{
public:
	NonrangeSelect() { }
	NonrangeSelect(std::optional<std::tuple<std::vector<std::tuple<MemberIdentifier, BitSelect>>, MemberIdentifier>> * _memberIdentifier, BitSelect * _bitSelect) { memberIdentifier = _memberIdentifier; bitSelect = _bitSelect; }

	std::optional<std::tuple<std::vector<std::tuple<MemberIdentifier, BitSelect>>, MemberIdentifier>> *memberIdentifier;
	BitSelect *bitSelect;
};

class NonrangeVariableLvalue
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<PackageScope>, HierarchicalVariableIdentifier, NonrangeSelect>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<ImplicitClassHandle>, HierarchicalVariableIdentifier, NonrangeSelect>>>::type v2;
public:
	NonrangeVariableLvalue() { }
	boost::make_variant_over<v2>::type choice;
};

class Notifier
{
public:
	Notifier() { }
	Notifier(VariableIdentifier * _variableIdentifier) { variableIdentifier = _variableIdentifier; }

	VariableIdentifier *variableIdentifier;
};
class Number
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<RealNumber>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<IntegralNumber>>::type v2;
public:
	Number() { }
	boost::make_variant_over<v2>::type choice;
};

typedef std::string OctalBase;
class OctalNumber
{
public:
	OctalNumber() { }
	OctalNumber(std::optional<Size> * _size, OctalBase * _octalBase, OctalValue * _octalValue) { size = _size; octalBase = _octalBase; octalValue = _octalValue; }

	std::optional<Size> *size;
	OctalBase *octalBase;
	OctalValue *octalValue;
};

typedef std::string OctalValue;
class OpenRangeList
{
public:
	OpenRangeList() { }
	OpenRangeList(OpenValueRange * _openValueRange) { openValueRange = _openValueRange; }

	OpenValueRange *openValueRange;
};
class OpenValueRange
{
public:
	OpenValueRange() { }
	OpenValueRange(ValueRange * _valueRange) { valueRange = _valueRange; }

	ValueRange *valueRange;
};
class OperatorAssignment
{
public:
	OperatorAssignment() { }
	OperatorAssignment(VariableLvalue * _variableLvalue, AssignmentOperator * _assignmentOperator, Expression * _expression) { variableLvalue = _variableLvalue; assignmentOperator = _assignmentOperator; expression = _expression; }

	VariableLvalue *variableLvalue;
	AssignmentOperator *assignmentOperator;
	Expression *expression;
};

class OrderedCheckerPortConnection
{
public:
	OrderedCheckerPortConnection() { }
	OrderedCheckerPortConnection(std::vector<AttributeInstance> * _attributeInstance, std::optional<PropertyActualArg> * _propertyActualArg) { attributeInstance = _attributeInstance; propertyActualArg = _propertyActualArg; }

	std::vector<AttributeInstance> *attributeInstance;
	std::optional<PropertyActualArg> *propertyActualArg;
};

class OrderedParameterAssignment
{
public:
	OrderedParameterAssignment() { }
	OrderedParameterAssignment(ParamExpression * _paramExpression) { paramExpression = _paramExpression; }

	ParamExpression *paramExpression;
};
class OrderedPortConnection
{
public:
	OrderedPortConnection() { }
	OrderedPortConnection(std::vector<AttributeInstance> * _attributeInstance, std::optional<Expression> * _expression) { attributeInstance = _attributeInstance; expression = _expression; }

	std::vector<AttributeInstance> *attributeInstance;
	std::optional<Expression> *expression;
};

class OutputDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<VariablePortType, ListOfPortIdentifiers>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<NetPortType, ListOfPortIdentifiers>>>::type v2;
public:
	OutputDeclaration() { }
	boost::make_variant_over<v2>::type choice;
};

class OutputIdentifier
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<InterfaceIdentifier, PortIdentifier>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<InoutPortIdentifier>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<OutputPortIdentifier>>::type v3;
public:
	OutputIdentifier() { }
	boost::make_variant_over<v3>::type choice;
};

class OutputPortIdentifier
{
public:
	OutputPortIdentifier() { }
	OutputPortIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class OutputSymbol
{
public:
	OutputSymbol() { }
	OutputSymbol(UnsignedNumber * _unsignedNumber) { unsignedNumber = _unsignedNumber; }

	UnsignedNumber *unsignedNumber;
};
class OutputTerminal
{
public:
	OutputTerminal() { }
	OutputTerminal(NetLvalue * _netLvalue) { netLvalue = _netLvalue; }

	NetLvalue *netLvalue;
};
class OverloadDeclaration
{
public:
	OverloadDeclaration() { }
	OverloadDeclaration(OverloadOperator * _overloadOperator, DataType * _dataType, FunctionIdentifier * _functionIdentifier, OverloadProtoFormals * _overloadProtoFormals) { overloadOperator = _overloadOperator; dataType = _dataType; functionIdentifier = _functionIdentifier; overloadProtoFormals = _overloadProtoFormals; }

	OverloadOperator *overloadOperator;
	DataType *dataType;
	FunctionIdentifier *functionIdentifier;
	OverloadProtoFormals *overloadProtoFormals;
};

enum class OverloadOperator
{
	Plus, Increment, Minus, Decrement, Star, Doublestar, Slash, Percent, Eq, Noteq, Lt, Lteq, Gt, Gteq, Assignop
};

class OverloadProtoFormals
{
public:
	OverloadProtoFormals() { }
	OverloadProtoFormals(DataType * _dataType) { dataType = _dataType; }

	DataType *dataType;
};
class PControlTerminal
{
public:
	PControlTerminal() { }
	PControlTerminal(Expression * _expression) { expression = _expression; }

	Expression *expression;
};
class PackageDeclaration
{
public:
	PackageDeclaration() { }
	PackageDeclaration(std::vector<AttributeInstance> * _attributeInstance0, std::optional<Lifetime> * _lifetime, PackageIdentifier * _packageIdentifier2, std::optional<TimeunitsDeclaration> * _timeunitsDeclaration, std::vector<std::tuple<std::vector<AttributeInstance>, PackageItem>> * _attributeInstance4, std::optional<PackageIdentifier> * _packageIdentifier5) { attributeInstance0 = _attributeInstance0; lifetime = _lifetime; packageIdentifier2 = _packageIdentifier2; timeunitsDeclaration = _timeunitsDeclaration; attributeInstance4 = _attributeInstance4; packageIdentifier5 = _packageIdentifier5; }

	std::vector<AttributeInstance> *attributeInstance0;
	std::optional<Lifetime> *lifetime;
	PackageIdentifier *packageIdentifier2;
	std::optional<TimeunitsDeclaration> *timeunitsDeclaration;
	std::vector<std::tuple<std::vector<AttributeInstance>, PackageItem>> *attributeInstance4;
	std::optional<PackageIdentifier> *packageIdentifier5;
};

class PackageExportDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::vector<PackageImportItem>>>::type v1;
public:
	PackageExportDeclaration() { }
	boost::make_variant_over<v1>::type choice;
};

class PackageIdentifier
{
public:
	PackageIdentifier() { }
	PackageIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class PackageImportDeclaration
{
public:
	PackageImportDeclaration() { }
	PackageImportDeclaration(std::vector<PackageImportItem> * _packageImportItem) { packageImportItem = _packageImportItem; }

	std::vector<PackageImportItem> *packageImportItem;
};

class PackageImportItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<PackageIdentifier>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<PackageIdentifier, Identifier>>>::type v2;
public:
	PackageImportItem() { }
	boost::make_variant_over<v2>::type choice;
};

class PackageItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<TimeunitsDeclaration>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<PackageExportDeclaration>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<AnonymousProgram>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<PackageOrGenerateItemDeclaration>>::type v4;
public:
	PackageItem() { }
	boost::make_variant_over<v4>::type choice;
};

class PackageOrGenerateItemDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<AssertionItemDeclaration>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<OverloadDeclaration>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<CovergroupDeclaration>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<ParameterDeclaration>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<LocalParameterDeclaration>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<ClassConstructorDeclaration>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<ClassDeclaration>>::type v7;
	typedef boost::mpl::push_front<v7, boost::recursive_wrapper<ExternConstraintDeclaration>>::type v8;
	typedef boost::mpl::push_front<v8, boost::recursive_wrapper<DpiImportExport>>::type v9;
	typedef boost::mpl::push_front<v9, boost::recursive_wrapper<CheckerDeclaration>>::type v10;
	typedef boost::mpl::push_front<v10, boost::recursive_wrapper<FunctionDeclaration>>::type v11;
	typedef boost::mpl::push_front<v11, boost::recursive_wrapper<TaskDeclaration>>::type v12;
	typedef boost::mpl::push_front<v12, boost::recursive_wrapper<DataDeclaration>>::type v13;
	typedef boost::mpl::push_front<v13, boost::recursive_wrapper<NetDeclaration>>::type v14;
public:
	PackageOrGenerateItemDeclaration() { }
	boost::make_variant_over<v14>::type choice;
};

class PackageScope
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<PackageIdentifier>>::type v1;
public:
	PackageScope() { }
	boost::make_variant_over<v1>::type choice;
};

class PackedDimension
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<UnsizedDimension>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ConstantRange>>::type v2;
public:
	PackedDimension() { }
	boost::make_variant_over<v2>::type choice;
};

class ParBlock
{
public:
	ParBlock() { }
	ParBlock(std::optional<BlockIdentifier> * _blockIdentifier0, std::vector<BlockItemDeclaration> * _blockItemDeclaration, std::vector<StatementOrNull> * _statementOrNull, JoinKeyword * _joinKeyword, std::optional<BlockIdentifier> * _blockIdentifier4) { blockIdentifier0 = _blockIdentifier0; blockItemDeclaration = _blockItemDeclaration; statementOrNull = _statementOrNull; joinKeyword = _joinKeyword; blockIdentifier4 = _blockIdentifier4; }

	std::optional<BlockIdentifier> *blockIdentifier0;
	std::vector<BlockItemDeclaration> *blockItemDeclaration;
	std::vector<StatementOrNull> *statementOrNull;
	JoinKeyword *joinKeyword;
	std::optional<BlockIdentifier> *blockIdentifier4;
};

class ParallelEdgeSensitivePathDescription
{
public:
	ParallelEdgeSensitivePathDescription() { }
	ParallelEdgeSensitivePathDescription(std::optional<EdgeIdentifier> * _edgeIdentifier, SpecifyInputTerminalDescriptor * _specifyInputTerminalDescriptor, std::optional<PolarityOperator> * _polarityOperator2, SpecifyOutputTerminalDescriptor * _specifyOutputTerminalDescriptor, std::optional<PolarityOperator> * _polarityOperator4, DataSourceExpression * _dataSourceExpression) { edgeIdentifier = _edgeIdentifier; specifyInputTerminalDescriptor = _specifyInputTerminalDescriptor; polarityOperator2 = _polarityOperator2; specifyOutputTerminalDescriptor = _specifyOutputTerminalDescriptor; polarityOperator4 = _polarityOperator4; dataSourceExpression = _dataSourceExpression; }

	std::optional<EdgeIdentifier> *edgeIdentifier;
	SpecifyInputTerminalDescriptor *specifyInputTerminalDescriptor;
	std::optional<PolarityOperator> *polarityOperator2;
	SpecifyOutputTerminalDescriptor *specifyOutputTerminalDescriptor;
	std::optional<PolarityOperator> *polarityOperator4;
	DataSourceExpression *dataSourceExpression;
};

class ParallelPathDescription
{
public:
	ParallelPathDescription() { }
	ParallelPathDescription(SpecifyInputTerminalDescriptor * _specifyInputTerminalDescriptor, std::optional<PolarityOperator> * _polarityOperator, SpecifyOutputTerminalDescriptor * _specifyOutputTerminalDescriptor) { specifyInputTerminalDescriptor = _specifyInputTerminalDescriptor; polarityOperator = _polarityOperator; specifyOutputTerminalDescriptor = _specifyOutputTerminalDescriptor; }

	SpecifyInputTerminalDescriptor *specifyInputTerminalDescriptor;
	std::optional<PolarityOperator> *polarityOperator;
	SpecifyOutputTerminalDescriptor *specifyOutputTerminalDescriptor;
};

class ParamAssignment
{
public:
	ParamAssignment() { }
	ParamAssignment(ParameterIdentifier * _parameterIdentifier, std::vector<UnpackedDimension> * _unpackedDimension, std::optional<ConstantParamExpression> * _constantParamExpression) { parameterIdentifier = _parameterIdentifier; unpackedDimension = _unpackedDimension; constantParamExpression = _constantParamExpression; }

	ParameterIdentifier *parameterIdentifier;
	std::vector<UnpackedDimension> *unpackedDimension;
	std::optional<ConstantParamExpression> *constantParamExpression;
};

class ParamExpression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<DataType>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<MintypmaxExpression>>::type v2;
public:
	ParamExpression() { }
	boost::make_variant_over<v2>::type choice;
};

class ParameterDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ListOfTypeAssignments>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<DataTypeOrImplicit, ListOfParamAssignments>>>::type v2;
public:
	ParameterDeclaration() { }
	boost::make_variant_over<v2>::type choice;
};

class ParameterIdentifier
{
public:
	ParameterIdentifier() { }
	ParameterIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class ParameterOverride
{
public:
	ParameterOverride() { }
	ParameterOverride(ListOfDefparamAssignments * _listOfDefparamAssignments) { listOfDefparamAssignments = _listOfDefparamAssignments; }

	ListOfDefparamAssignments *listOfDefparamAssignments;
};

class ParameterPortDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ListOfTypeAssignments>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<DataType, ListOfParamAssignments>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<LocalParameterDeclaration>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<ParameterDeclaration>>::type v4;
public:
	ParameterPortDeclaration() { }
	boost::make_variant_over<v4>::type choice;
};

class ParameterPortList
{
public:
	ParameterPortList() { }
	ParameterPortList(std::optional<ListOfParamAssignments> * _listOfParamAssignments, std::vector<ParameterPortDeclaration> * _parameterPortDeclaration) { listOfParamAssignments = _listOfParamAssignments; parameterPortDeclaration = _parameterPortDeclaration; }

	std::optional<ListOfParamAssignments> *listOfParamAssignments;
	std::vector<ParameterPortDeclaration> *parameterPortDeclaration;
};

class ParameterValueAssignment
{
public:
	ParameterValueAssignment() { }
	ParameterValueAssignment(std::optional<ListOfParameterAssignments> * _listOfParameterAssignments) { listOfParameterAssignments = _listOfParameterAssignments; }

	std::optional<ListOfParameterAssignments> *listOfParameterAssignments;
};

class PartSelectRange
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<IndexedRange>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ConstantRange>>::type v2;
public:
	PartSelectRange() { }
	boost::make_variant_over<v2>::type choice;
};

enum class PassEnSwitchType
{
	Tranif0, Tranif1, Rtranif1, Rtranif0
};

class PassEnableSwitchInstance
{
public:
	PassEnableSwitchInstance() { }
	PassEnableSwitchInstance(std::optional<NameOfInstance> * _nameOfInstance, InoutTerminal * _inoutTerminal1, InoutTerminal * _inoutTerminal2, EnableTerminal * _enableTerminal) { nameOfInstance = _nameOfInstance; inoutTerminal1 = _inoutTerminal1; inoutTerminal2 = _inoutTerminal2; enableTerminal = _enableTerminal; }

	std::optional<NameOfInstance> *nameOfInstance;
	InoutTerminal *inoutTerminal1;
	InoutTerminal *inoutTerminal2;
	EnableTerminal *enableTerminal;
};

class PassSwitchInstance
{
public:
	PassSwitchInstance() { }
	PassSwitchInstance(std::optional<NameOfInstance> * _nameOfInstance, InoutTerminal * _inoutTerminal1, InoutTerminal * _inoutTerminal2) { nameOfInstance = _nameOfInstance; inoutTerminal1 = _inoutTerminal1; inoutTerminal2 = _inoutTerminal2; }

	std::optional<NameOfInstance> *nameOfInstance;
	InoutTerminal *inoutTerminal1;
	InoutTerminal *inoutTerminal2;
};

enum class PassSwitchtype
{
	Tran, Rtran
};

class PathDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<StateDependentPathDeclaration>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<EdgeSensitivePathDeclaration>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<SimplePathDeclaration>>::type v3;
public:
	PathDeclaration() { }
	boost::make_variant_over<v3>::type choice;
};

class PathDelayExpression
{
public:
	PathDelayExpression() { }
	PathDelayExpression(ConstantMintypmaxExpression * _constantMintypmaxExpression) { constantMintypmaxExpression = _constantMintypmaxExpression; }

	ConstantMintypmaxExpression *constantMintypmaxExpression;
};
class PathDelayValue
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ListOfPathDelayExpressions>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ListOfPathDelayExpressions>>::type v2;
public:
	PathDelayValue() { }
	boost::make_variant_over<v2>::type choice;
};

class Pattern
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::vector<std::tuple<MemberIdentifier, Pattern>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::vector<Pattern>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<MemberIdentifier, std::optional<Pattern>>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<ConstantExpression>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<VariableIdentifier>>::type v5;
public:
	Pattern() { }
	boost::make_variant_over<v5>::type choice;
};

class PeriodTimingCheck
{
public:
	PeriodTimingCheck() { }
	PeriodTimingCheck(ControlledReferenceEvent * _controlledReferenceEvent, TimingCheckLimit * _timingCheckLimit, std::optional<std::optional<Notifier>> * _notifier) { controlledReferenceEvent = _controlledReferenceEvent; timingCheckLimit = _timingCheckLimit; notifier = _notifier; }

	ControlledReferenceEvent *controlledReferenceEvent;
	TimingCheckLimit *timingCheckLimit;
	std::optional<std::optional<Notifier>> *notifier;
};

enum class PolarityOperator
{
	Plus, Minus
};

class Port
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::optional<PortExpression>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<PortIdentifier, std::optional<PortExpression>>>>::type v2;
public:
	Port() { }
	boost::make_variant_over<v2>::type choice;
};

class PortDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, InterfacePortDeclaration>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, RefDeclaration>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, OutputDeclaration>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, InputDeclaration>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, InoutDeclaration>>>::type v5;
public:
	PortDeclaration() { }
	boost::make_variant_over<v5>::type choice;
};

enum class PortDirection
{
	Inout, Input, Output, Ref
};

class PortExpression
{
public:
	PortExpression() { }
	PortExpression(PortReference * _portReference) { portReference = _portReference; }

	PortReference *portReference;
};
class PortIdentifier
{
public:
	PortIdentifier() { }
	PortIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class PortReference
{
public:
	PortReference() { }
	PortReference(PortIdentifier * _portIdentifier, ConstantSelect * _constantSelect) { portIdentifier = _portIdentifier; constantSelect = _constantSelect; }

	PortIdentifier *portIdentifier;
	ConstantSelect *constantSelect;
};

class Primary
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<SequenceMethodCall>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<StreamingConcatenation>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<AssignmentPatternExpression>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<Cast>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<MintypmaxExpression>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<LetExpression>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<FunctionSubroutineCall>>::type v7;
	typedef boost::mpl::push_front<v7, boost::recursive_wrapper<std::tuple<MultipleConcatenation, std::optional<RangeExpression>>>>::type v8;
	typedef boost::mpl::push_front<v8, boost::recursive_wrapper<std::tuple<Concatenation, std::optional<RangeExpression>>>>::type v9;
	typedef boost::mpl::push_front<v9, boost::recursive_wrapper<EmptyQueue>>::type v10;
	typedef boost::mpl::push_front<v10, boost::recursive_wrapper<std::tuple<std::optional<PackageScope>, HierarchicalIdentifier, Select>>>::type v11;
	typedef boost::mpl::push_front<v11, boost::recursive_wrapper<std::tuple<std::optional<ClassQualifier>, HierarchicalIdentifier, Select>>>::type v12;
	typedef boost::mpl::push_front<v12, boost::recursive_wrapper<PrimaryLiteral>>::type v13;
public:
	Primary() { }
	boost::make_variant_over<v13>::type choice;
};

class PrimaryLiteral
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<StringLiteral>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<UnbasedUnsizedLiteral>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<TimeLiteral>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<Number>>::type v4;
public:
	PrimaryLiteral() { }
	boost::make_variant_over<v4>::type choice;
};

class ProceduralAssertionStatement
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<CheckerInstantiation>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ImmediateAssertionStatement>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<ConcurrentAssertionStatement>>::type v3;
public:
	ProceduralAssertionStatement() { }
	boost::make_variant_over<v3>::type choice;
};

class ProceduralContinuousAssignment
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<NetLvalue>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<VariableLvalue>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<NetAssignment>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<VariableAssignment>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<VariableLvalue>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<VariableAssignment>>::type v6;
public:
	ProceduralContinuousAssignment() { }
	boost::make_variant_over<v6>::type choice;
};

class ProceduralTimingControl
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<CycleDelay>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<EventControl>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<DelayControl>>::type v3;
public:
	ProceduralTimingControl() { }
	boost::make_variant_over<v3>::type choice;
};

class ProceduralTimingControlStatement
{
public:
	ProceduralTimingControlStatement() { }
	ProceduralTimingControlStatement(ProceduralTimingControl * _proceduralTimingControl, StatementOrNull * _statementOrNull) { proceduralTimingControl = _proceduralTimingControl; statementOrNull = _statementOrNull; }

	ProceduralTimingControl *proceduralTimingControl;
	StatementOrNull *statementOrNull;
};

class Production
{
public:
	Production() { }
	Production(std::optional<DataTypeOrVoid> * _dataTypeOrVoid, ProductionIdentifier * _productionIdentifier, std::optional<TfPortList> * _tfPortList, std::vector<RsRule> * _rsRule) { dataTypeOrVoid = _dataTypeOrVoid; productionIdentifier = _productionIdentifier; tfPortList = _tfPortList; rsRule = _rsRule; }

	std::optional<DataTypeOrVoid> *dataTypeOrVoid;
	ProductionIdentifier *productionIdentifier;
	std::optional<TfPortList> *tfPortList;
	std::vector<RsRule> *rsRule;
};

class ProductionIdentifier
{
public:
	ProductionIdentifier() { }
	ProductionIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class ProductionItem
{
public:
	ProductionItem() { }
	ProductionItem(ProductionIdentifier * _productionIdentifier, std::optional<ListOfArguments> * _listOfArguments) { productionIdentifier = _productionIdentifier; listOfArguments = _listOfArguments; }

	ProductionIdentifier *productionIdentifier;
	std::optional<ListOfArguments> *listOfArguments;
};

class ProgramAnsiHeader
{
public:
	ProgramAnsiHeader() { }
	ProgramAnsiHeader(std::vector<AttributeInstance> * _attributeInstance, std::optional<Lifetime> * _lifetime, ProgramIdentifier * _programIdentifier, std::vector<PackageImportDeclaration> * _packageImportDeclaration, std::optional<ParameterPortList> * _parameterPortList, std::optional<ListOfPortDeclarations> * _listOfPortDeclarations) { attributeInstance = _attributeInstance; lifetime = _lifetime; programIdentifier = _programIdentifier; packageImportDeclaration = _packageImportDeclaration; parameterPortList = _parameterPortList; listOfPortDeclarations = _listOfPortDeclarations; }

	std::vector<AttributeInstance> *attributeInstance;
	std::optional<Lifetime> *lifetime;
	ProgramIdentifier *programIdentifier;
	std::vector<PackageImportDeclaration> *packageImportDeclaration;
	std::optional<ParameterPortList> *parameterPortList;
	std::optional<ListOfPortDeclarations> *listOfPortDeclarations;
};

class ProgramDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ProgramAnsiHeader>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ProgramNonAnsiHeader>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, ProgramIdentifier, std::optional<TimeunitsDeclaration>, std::vector<ProgramItem>, std::optional<ProgramIdentifier>>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<ProgramAnsiHeader, std::optional<TimeunitsDeclaration>, std::vector<NonPortProgramItem>, std::optional<ProgramIdentifier>>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<ProgramNonAnsiHeader, std::optional<TimeunitsDeclaration>, std::vector<ProgramItem>, std::optional<ProgramIdentifier>>>>::type v5;
public:
	ProgramDeclaration() { }
	boost::make_variant_over<v5>::type choice;
};

class ProgramGenerateItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ElaborationSystemTask>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<GenerateRegion>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<ConditionalGenerateConstruct>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<LoopGenerateConstruct>>::type v4;
public:
	ProgramGenerateItem() { }
	boost::make_variant_over<v4>::type choice;
};

class ProgramIdentifier
{
public:
	ProgramIdentifier() { }
	ProgramIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class ProgramInstantiation
{
public:
	ProgramInstantiation() { }
	ProgramInstantiation(ProgramIdentifier * _programIdentifier, std::optional<ParameterValueAssignment> * _parameterValueAssignment, std::vector<HierarchicalInstance> * _hierarchicalInstance) { programIdentifier = _programIdentifier; parameterValueAssignment = _parameterValueAssignment; hierarchicalInstance = _hierarchicalInstance; }

	ProgramIdentifier *programIdentifier;
	std::optional<ParameterValueAssignment> *parameterValueAssignment;
	std::vector<HierarchicalInstance> *hierarchicalInstance;
};

class ProgramItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<NonPortProgramItem>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<PortDeclaration>>::type v2;
public:
	ProgramItem() { }
	boost::make_variant_over<v2>::type choice;
};

class ProgramNonAnsiHeader
{
public:
	ProgramNonAnsiHeader() { }
	ProgramNonAnsiHeader(std::vector<AttributeInstance> * _attributeInstance, std::optional<Lifetime> * _lifetime, ProgramIdentifier * _programIdentifier, std::vector<PackageImportDeclaration> * _packageImportDeclaration, std::optional<ParameterPortList> * _parameterPortList, ListOfPorts * _listOfPorts) { attributeInstance = _attributeInstance; lifetime = _lifetime; programIdentifier = _programIdentifier; packageImportDeclaration = _packageImportDeclaration; parameterPortList = _parameterPortList; listOfPorts = _listOfPorts; }

	std::vector<AttributeInstance> *attributeInstance;
	std::optional<Lifetime> *lifetime;
	ProgramIdentifier *programIdentifier;
	std::vector<PackageImportDeclaration> *packageImportDeclaration;
	std::optional<ParameterPortList> *parameterPortList;
	ListOfPorts *listOfPorts;
};

class PropertyActualArg
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<SequenceActualArg>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<PropertyExpr>>::type v2;
public:
	PropertyActualArg() { }
	boost::make_variant_over<v2>::type choice;
};

class PropertyCaseItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<PropertyExpr>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<ExpressionOrDist>, PropertyExpr>>>::type v2;
public:
	PropertyCaseItem() { }
	boost::make_variant_over<v2>::type choice;
};

class PropertyDeclaration
{
public:
	PropertyDeclaration() { }
	PropertyDeclaration(PropertyIdentifier * _propertyIdentifier0, std::optional<std::optional<PropertyPortList>> * _propertyPortList, std::vector<AssertionVariableDeclaration> * _assertionVariableDeclaration, PropertySpec * _propertySpec, std::optional<PropertyIdentifier> * _propertyIdentifier4) { propertyIdentifier0 = _propertyIdentifier0; propertyPortList = _propertyPortList; assertionVariableDeclaration = _assertionVariableDeclaration; propertySpec = _propertySpec; propertyIdentifier4 = _propertyIdentifier4; }

	PropertyIdentifier *propertyIdentifier0;
	std::optional<std::optional<PropertyPortList>> *propertyPortList;
	std::vector<AssertionVariableDeclaration> *assertionVariableDeclaration;
	PropertySpec *propertySpec;
	std::optional<PropertyIdentifier> *propertyIdentifier4;
};

class PropertyExpr
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<ClockingEvent, PropertyExpr>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<PropertyInstance>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<ExpressionOrDist, PropertyExpr>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<ExpressionOrDist, PropertyExpr>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<ExpressionOrDist, PropertyExpr>>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<std::tuple<ExpressionOrDist, PropertyExpr>>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<std::tuple<PropertyExpr, PropertyExpr>>>::type v7;
	typedef boost::mpl::push_front<v7, boost::recursive_wrapper<std::tuple<PropertyExpr, PropertyExpr>>>::type v8;
	typedef boost::mpl::push_front<v8, boost::recursive_wrapper<std::tuple<PropertyExpr, PropertyExpr>>>::type v9;
	typedef boost::mpl::push_front<v9, boost::recursive_wrapper<std::tuple<PropertyExpr, PropertyExpr>>>::type v10;
	typedef boost::mpl::push_front<v10, boost::recursive_wrapper<std::tuple<PropertyExpr, PropertyExpr>>>::type v11;
	typedef boost::mpl::push_front<v11, boost::recursive_wrapper<std::tuple<PropertyExpr, PropertyExpr>>>::type v12;
	typedef boost::mpl::push_front<v12, boost::recursive_wrapper<std::tuple<std::optional<CycleDelayConstRangeExpression>, PropertyExpr>>>::type v13;
	typedef boost::mpl::push_front<v13, boost::recursive_wrapper<std::tuple<ConstantRange, PropertyExpr>>>::type v14;
	typedef boost::mpl::push_front<v14, boost::recursive_wrapper<std::tuple<ConstantRange, PropertyExpr>>>::type v15;
	typedef boost::mpl::push_front<v15, boost::recursive_wrapper<std::tuple<std::optional<CycleDelayConstRangeExpression>, PropertyExpr>>>::type v16;
	typedef boost::mpl::push_front<v16, boost::recursive_wrapper<std::tuple<std::optional<ConstantExpression>, PropertyExpr>>>::type v17;
	typedef boost::mpl::push_front<v17, boost::recursive_wrapper<std::tuple<std::optional<ConstantExpression>, PropertyExpr>>>::type v18;
	typedef boost::mpl::push_front<v18, boost::recursive_wrapper<std::tuple<SequenceExpr, PropertyExpr>>>::type v19;
	typedef boost::mpl::push_front<v19, boost::recursive_wrapper<std::tuple<SequenceExpr, PropertyExpr>>>::type v20;
	typedef boost::mpl::push_front<v20, boost::recursive_wrapper<std::tuple<ExpressionOrDist, std::vector<PropertyCaseItem>>>>::type v21;
	typedef boost::mpl::push_front<v21, boost::recursive_wrapper<std::tuple<ExpressionOrDist, PropertyExpr, std::optional<PropertyExpr>>>>::type v22;
	typedef boost::mpl::push_front<v22, boost::recursive_wrapper<std::tuple<SequenceExpr, PropertyExpr>>>::type v23;
	typedef boost::mpl::push_front<v23, boost::recursive_wrapper<std::tuple<SequenceExpr, PropertyExpr>>>::type v24;
	typedef boost::mpl::push_front<v24, boost::recursive_wrapper<std::tuple<PropertyExpr, PropertyExpr>>>::type v25;
	typedef boost::mpl::push_front<v25, boost::recursive_wrapper<std::tuple<PropertyExpr, PropertyExpr>>>::type v26;
	typedef boost::mpl::push_front<v26, boost::recursive_wrapper<PropertyExpr>>::type v27;
	typedef boost::mpl::push_front<v27, boost::recursive_wrapper<PropertyExpr>>::type v28;
	typedef boost::mpl::push_front<v28, boost::recursive_wrapper<SequenceExpr>>::type v29;
	typedef boost::mpl::push_front<v29, boost::recursive_wrapper<SequenceExpr>>::type v30;
	typedef boost::mpl::push_front<v30, boost::recursive_wrapper<SequenceExpr>>::type v31;
public:
	PropertyExpr() { }
	boost::make_variant_over<v31>::type choice;
};

class PropertyFormalType
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<SequenceFormalType>>::type v1;
public:
	PropertyFormalType() { }
	boost::make_variant_over<v1>::type choice;
};

class PropertyIdentifier
{
public:
	PropertyIdentifier() { }
	PropertyIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class PropertyInstance
{
public:
	PropertyInstance() { }
	PropertyInstance(PsOrHierarchicalPropertyIdentifier * _psOrHierarchicalPropertyIdentifier, std::optional<std::optional<PropertyListOfArguments>> * _propertyListOfArguments) { psOrHierarchicalPropertyIdentifier = _psOrHierarchicalPropertyIdentifier; propertyListOfArguments = _propertyListOfArguments; }

	PsOrHierarchicalPropertyIdentifier *psOrHierarchicalPropertyIdentifier;
	std::optional<std::optional<PropertyListOfArguments>> *propertyListOfArguments;
};

class PropertyListOfArguments
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::vector<std::tuple<Identifier, std::optional<PropertyActualArg>>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<std::optional<PropertyActualArg>>, std::optional<std::vector<std::tuple<Identifier, std::optional<PropertyActualArg>>>>>>>::type v2;
public:
	PropertyListOfArguments() { }
	boost::make_variant_over<v2>::type choice;
};

enum class PropertyLvarPortDirection
{
	Input
};

class PropertyPortItem
{
public:
	PropertyPortItem() { }
	PropertyPortItem(std::vector<AttributeInstance> * _attributeInstance, std::optional<std::optional<PropertyLvarPortDirection>> * _propertyLvarPortDirection, PropertyFormalType * _propertyFormalType, FormalPortIdentifier * _formalPortIdentifier, std::vector<VariableDimension> * _variableDimension, std::optional<PropertyActualArg> * _propertyActualArg) { attributeInstance = _attributeInstance; propertyLvarPortDirection = _propertyLvarPortDirection; propertyFormalType = _propertyFormalType; formalPortIdentifier = _formalPortIdentifier; variableDimension = _variableDimension; propertyActualArg = _propertyActualArg; }

	std::vector<AttributeInstance> *attributeInstance;
	std::optional<std::optional<PropertyLvarPortDirection>> *propertyLvarPortDirection;
	PropertyFormalType *propertyFormalType;
	FormalPortIdentifier *formalPortIdentifier;
	std::vector<VariableDimension> *variableDimension;
	std::optional<PropertyActualArg> *propertyActualArg;
};

class PropertyPortList
{
public:
	PropertyPortList() { }
	PropertyPortList(PropertyPortItem * _propertyPortItem) { propertyPortItem = _propertyPortItem; }

	PropertyPortItem *propertyPortItem;
};
class PropertyQualifier
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ClassItemQualifier>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<RandomQualifier>>::type v2;
public:
	PropertyQualifier() { }
	boost::make_variant_over<v2>::type choice;
};

class PropertySpec
{
public:
	PropertySpec() { }
	PropertySpec(std::optional<ClockingEvent> * _clockingEvent, std::optional<ExpressionOrDist> * _expressionOrDist, PropertyExpr * _propertyExpr) { clockingEvent = _clockingEvent; expressionOrDist = _expressionOrDist; propertyExpr = _propertyExpr; }

	std::optional<ClockingEvent> *clockingEvent;
	std::optional<ExpressionOrDist> *expressionOrDist;
	PropertyExpr *propertyExpr;
};

class PsCheckerIdentifier
{
public:
	PsCheckerIdentifier() { }
	PsCheckerIdentifier(std::optional<PackageScope> * _packageScope, CheckerIdentifier * _checkerIdentifier) { packageScope = _packageScope; checkerIdentifier = _checkerIdentifier; }

	std::optional<PackageScope> *packageScope;
	CheckerIdentifier *checkerIdentifier;
};

class PsClassIdentifier
{
public:
	PsClassIdentifier() { }
	PsClassIdentifier(std::optional<PackageScope> * _packageScope, ClassIdentifier * _classIdentifier) { packageScope = _packageScope; classIdentifier = _classIdentifier; }

	std::optional<PackageScope> *packageScope;
	ClassIdentifier *classIdentifier;
};

class PsCovergroupIdentifier
{
public:
	PsCovergroupIdentifier() { }
	PsCovergroupIdentifier(std::optional<PackageScope> * _packageScope, CovergroupIdentifier * _covergroupIdentifier) { packageScope = _packageScope; covergroupIdentifier = _covergroupIdentifier; }

	std::optional<PackageScope> *packageScope;
	CovergroupIdentifier *covergroupIdentifier;
};

class PsIdentifier
{
public:
	PsIdentifier() { }
	PsIdentifier(std::optional<PackageScope> * _packageScope, Identifier * _identifier) { packageScope = _packageScope; identifier = _identifier; }

	std::optional<PackageScope> *packageScope;
	Identifier *identifier;
};

class PsOrHierarchicalArrayIdentifier
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<PackageScope, HierarchicalArrayIdentifier>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<ClassScope, HierarchicalArrayIdentifier>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<ImplicitClassHandle, HierarchicalArrayIdentifier>>>::type v3;
public:
	PsOrHierarchicalArrayIdentifier() { }
	boost::make_variant_over<v3>::type choice;
};

class PsOrHierarchicalNetIdentifier
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<HierarchicalNetIdentifier>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<PackageScope>, NetIdentifier>>>::type v2;
public:
	PsOrHierarchicalNetIdentifier() { }
	boost::make_variant_over<v2>::type choice;
};

class PsOrHierarchicalPropertyIdentifier
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<HierarchicalPropertyIdentifier>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<PackageScope>, PropertyIdentifier>>>::type v2;
public:
	PsOrHierarchicalPropertyIdentifier() { }
	boost::make_variant_over<v2>::type choice;
};

class PsOrHierarchicalSequenceIdentifier
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<HierarchicalSequenceIdentifier>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<PackageScope>, SequenceIdentifier>>>::type v2;
public:
	PsOrHierarchicalSequenceIdentifier() { }
	boost::make_variant_over<v2>::type choice;
};

class PsOrHierarchicalTfIdentifier
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<HierarchicalTfIdentifier>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<PackageScope>, TfIdentifier>>>::type v2;
public:
	PsOrHierarchicalTfIdentifier() { }
	boost::make_variant_over<v2>::type choice;
};

class PsParameterIdentifier
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::vector<std::tuple<GenerateBlockIdentifier, std::optional<ConstantExpression>>>, ParameterIdentifier>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<ClassScope>, ParameterIdentifier>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::optional<PackageScope>, ParameterIdentifier>>>::type v3;
public:
	PsParameterIdentifier() { }
	boost::make_variant_over<v3>::type choice;
};

class PsTypeIdentifier
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<PackageScope>, TypeIdentifier>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<int>, TypeIdentifier>>>::type v2;
public:
	PsTypeIdentifier() { }
	boost::make_variant_over<v2>::type choice;
};

class PullGateInstance
{
public:
	PullGateInstance() { }
	PullGateInstance(std::optional<NameOfInstance> * _nameOfInstance, OutputTerminal * _outputTerminal) { nameOfInstance = _nameOfInstance; outputTerminal = _outputTerminal; }

	std::optional<NameOfInstance> *nameOfInstance;
	OutputTerminal *outputTerminal;
};

class PulldownStrength
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<Strength0>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<Strength1, Strength0>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<Strength0, Strength1>>>::type v3;
public:
	PulldownStrength() { }
	boost::make_variant_over<v3>::type choice;
};

class PullupStrength
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<Strength1>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<Strength1, Strength0>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<Strength0, Strength1>>>::type v3;
public:
	PullupStrength() { }
	boost::make_variant_over<v3>::type choice;
};

class PulseControlSpecparam
{
public:
	PulseControlSpecparam() { }
	PulseControlSpecparam(RejectLimitValue * _rejectLimitValue, std::optional<ErrorLimitValue> * _errorLimitValue) { rejectLimitValue = _rejectLimitValue; errorLimitValue = _errorLimitValue; }

	RejectLimitValue *rejectLimitValue;
	std::optional<ErrorLimitValue> *errorLimitValue;
};

class PulsestyleDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ListOfPathOutputs>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ListOfPathOutputs>>::type v2;
public:
	PulsestyleDeclaration() { }
	boost::make_variant_over<v2>::type choice;
};

class QueueDimension
{
public:
	QueueDimension() { }
	QueueDimension(std::optional<ConstantExpression> * _constantExpression) { constantExpression = _constantExpression; }

	std::optional<ConstantExpression> *constantExpression;
};

class RandcaseItem
{
public:
	RandcaseItem() { }
	RandcaseItem(Expression * _expression, StatementOrNull * _statementOrNull) { expression = _expression; statementOrNull = _statementOrNull; }

	Expression *expression;
	StatementOrNull *statementOrNull;
};

class RandcaseStatement
{
public:
	RandcaseStatement() { }
	RandcaseStatement(std::vector<RandcaseItem> * _randcaseItem) { randcaseItem = _randcaseItem; }

	std::vector<RandcaseItem> *randcaseItem;
};

enum class RandomQualifier
{
	Rand, Randc
};

class RandomizeCall
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, std::optional<int>, std::optional<std::tuple<std::optional<std::optional<IdentifierList>>, ConstraintBlock>>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, std::optional<std::optional<VariableIdentifierList>>, std::optional<std::tuple<std::optional<std::optional<IdentifierList>>, ConstraintBlock>>>>>::type v2;
public:
	RandomizeCall() { }
	boost::make_variant_over<v2>::type choice;
};

class RandsequenceStatement
{
public:
	RandsequenceStatement() { }
	RandsequenceStatement(std::optional<ProductionIdentifier> * _productionIdentifier, std::vector<Production> * _production) { productionIdentifier = _productionIdentifier; production = _production; }

	std::optional<ProductionIdentifier> *productionIdentifier;
	std::vector<Production> *production;
};

class RangeExpression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<PartSelectRange>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<Expression>>::type v2;
public:
	RangeExpression() { }
	boost::make_variant_over<v2>::type choice;
};

class RealNumber
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<UnsignedNumber, std::optional<UnsignedNumber>, std::optional<Sign>, UnsignedNumber>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<FixedPointNumber>>::type v2;
public:
	RealNumber() { }
	boost::make_variant_over<v2>::type choice;
};

class RecoveryTimingCheck
{
public:
	RecoveryTimingCheck() { }
	RecoveryTimingCheck(ReferenceEvent * _referenceEvent, DataEvent * _dataEvent, TimingCheckLimit * _timingCheckLimit, std::optional<std::optional<Notifier>> * _notifier) { referenceEvent = _referenceEvent; dataEvent = _dataEvent; timingCheckLimit = _timingCheckLimit; notifier = _notifier; }

	ReferenceEvent *referenceEvent;
	DataEvent *dataEvent;
	TimingCheckLimit *timingCheckLimit;
	std::optional<std::optional<Notifier>> *notifier;
};

class RecremTimingCheck
{
public:
	RecremTimingCheck() { }
	RecremTimingCheck(ReferenceEvent * _referenceEvent, DataEvent * _dataEvent, TimingCheckLimit * _timingCheckLimit2, TimingCheckLimit * _timingCheckLimit3, std::optional<std::tuple<std::optional<Notifier>, std::optional<std::tuple<std::optional<TimestampCondition>, std::optional<std::tuple<std::optional<TimecheckCondition>, std::optional<std::tuple<std::optional<DelayedReference>, std::optional<std::optional<DelayedData>>>>>>>>>> * _notifier) { referenceEvent = _referenceEvent; dataEvent = _dataEvent; timingCheckLimit2 = _timingCheckLimit2; timingCheckLimit3 = _timingCheckLimit3; notifier = _notifier; }

	ReferenceEvent *referenceEvent;
	DataEvent *dataEvent;
	TimingCheckLimit *timingCheckLimit2;
	TimingCheckLimit *timingCheckLimit3;
	std::optional<std::tuple<std::optional<Notifier>, std::optional<std::tuple<std::optional<TimestampCondition>, std::optional<std::tuple<std::optional<TimecheckCondition>, std::optional<std::tuple<std::optional<DelayedReference>, std::optional<std::optional<DelayedData>>>>>>>>>> *notifier;
};

class RefDeclaration
{
public:
	RefDeclaration() { }
	RefDeclaration(VariablePortType * _variablePortType, ListOfVariableIdentifiers * _listOfVariableIdentifiers) { variablePortType = _variablePortType; listOfVariableIdentifiers = _listOfVariableIdentifiers; }

	VariablePortType *variablePortType;
	ListOfVariableIdentifiers *listOfVariableIdentifiers;
};

class ReferenceEvent
{
public:
	ReferenceEvent() { }
	ReferenceEvent(TimingCheckEvent * _timingCheckEvent) { timingCheckEvent = _timingCheckEvent; }

	TimingCheckEvent *timingCheckEvent;
};
class RejectLimitValue
{
public:
	RejectLimitValue() { }
	RejectLimitValue(LimitValue * _limitValue) { limitValue = _limitValue; }

	LimitValue *limitValue;
};
class RemainActiveFlag
{
public:
	RemainActiveFlag() { }
	RemainActiveFlag(ConstantMintypmaxExpression * _constantMintypmaxExpression) { constantMintypmaxExpression = _constantMintypmaxExpression; }

	ConstantMintypmaxExpression *constantMintypmaxExpression;
};
class RemovalTimingCheck
{
public:
	RemovalTimingCheck() { }
	RemovalTimingCheck(ReferenceEvent * _referenceEvent, DataEvent * _dataEvent, TimingCheckLimit * _timingCheckLimit, std::optional<std::optional<Notifier>> * _notifier) { referenceEvent = _referenceEvent; dataEvent = _dataEvent; timingCheckLimit = _timingCheckLimit; notifier = _notifier; }

	ReferenceEvent *referenceEvent;
	DataEvent *dataEvent;
	TimingCheckLimit *timingCheckLimit;
	std::optional<std::optional<Notifier>> *notifier;
};

class RepeatRange
{
public:
	RepeatRange() { }
	RepeatRange(CovergroupExpression * _covergroupExpression0, std::optional<CovergroupExpression> * _covergroupExpression1) { covergroupExpression0 = _covergroupExpression0; covergroupExpression1 = _covergroupExpression1; }

	CovergroupExpression *covergroupExpression0;
	std::optional<CovergroupExpression> *covergroupExpression1;
};

class RestrictPropertyStatement
{
public:
	RestrictPropertyStatement() { }
	RestrictPropertyStatement(PropertySpec * _propertySpec) { propertySpec = _propertySpec; }

	PropertySpec *propertySpec;
};

class RsCase
{
public:
	RsCase() { }
	RsCase(CaseExpression * _caseExpression, std::vector<RsCaseItem> * _rsCaseItem) { caseExpression = _caseExpression; rsCaseItem = _rsCaseItem; }

	CaseExpression *caseExpression;
	std::vector<RsCaseItem> *rsCaseItem;
};

class RsCaseItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ProductionItem>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<CaseItemExpression>, ProductionItem>>>::type v2;
public:
	RsCaseItem() { }
	boost::make_variant_over<v2>::type choice;
};

class RsCodeBlock
{
public:
	RsCodeBlock() { }
	RsCodeBlock(std::vector<DataDeclaration> * _dataDeclaration, std::vector<StatementOrNull> * _statementOrNull) { dataDeclaration = _dataDeclaration; statementOrNull = _statementOrNull; }

	std::vector<DataDeclaration> *dataDeclaration;
	std::vector<StatementOrNull> *statementOrNull;
};

class RsIfElse
{
public:
	RsIfElse() { }
	RsIfElse(Expression * _expression, ProductionItem * _productionItem1, std::optional<ProductionItem> * _productionItem2) { expression = _expression; productionItem1 = _productionItem1; productionItem2 = _productionItem2; }

	Expression *expression;
	ProductionItem *productionItem1;
	std::optional<ProductionItem> *productionItem2;
};

class RsProd
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<RsCase>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<RsRepeat>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<RsIfElse>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<RsCodeBlock>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<ProductionItem>>::type v5;
public:
	RsProd() { }
	boost::make_variant_over<v5>::type choice;
};

class RsProductionList
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<Expression>, ProductionItem, std::vector<ProductionItem>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::vector<RsProd>>>::type v2;
public:
	RsProductionList() { }
	boost::make_variant_over<v2>::type choice;
};

class RsRepeat
{
public:
	RsRepeat() { }
	RsRepeat(Expression * _expression, ProductionItem * _productionItem) { expression = _expression; productionItem = _productionItem; }

	Expression *expression;
	ProductionItem *productionItem;
};

class RsRule
{
public:
	RsRule() { }
	RsRule(RsProductionList * _rsProductionList, std::optional<std::tuple<WeightSpecification, std::optional<RsCodeBlock>>> * _weightSpecification) { rsProductionList = _rsProductionList; weightSpecification = _weightSpecification; }

	RsProductionList *rsProductionList;
	std::optional<std::tuple<WeightSpecification, std::optional<RsCodeBlock>>> *weightSpecification;
};

class ScalarConstant
{
public:
	ScalarConstant() { }
	ScalarConstant(Number * _number) { number = _number; }

	Number *number;
};
class ScalarTimingCheckCondition
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<Expression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<Expression, ScalarConstant>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<Expression, ScalarConstant>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<Expression, ScalarConstant>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<Expression, ScalarConstant>>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<Expression>>::type v6;
public:
	ScalarTimingCheckCondition() { }
	boost::make_variant_over<v6>::type choice;
};

class Select
{
public:
	Select() { }
	Select(std::optional<std::tuple<std::vector<std::tuple<MemberIdentifier, BitSelect>>, MemberIdentifier>> * _memberIdentifier, BitSelect * _bitSelect, std::optional<PartSelectRange> * _partSelectRange) { memberIdentifier = _memberIdentifier; bitSelect = _bitSelect; partSelectRange = _partSelectRange; }

	std::optional<std::tuple<std::vector<std::tuple<MemberIdentifier, BitSelect>>, MemberIdentifier>> *memberIdentifier;
	BitSelect *bitSelect;
	std::optional<PartSelectRange> *partSelectRange;
};

class SelectCondition
{
public:
	SelectCondition() { }
	SelectCondition(BinsExpression * _binsExpression, std::optional<CovergroupRangeList> * _covergroupRangeList) { binsExpression = _binsExpression; covergroupRangeList = _covergroupRangeList; }

	BinsExpression *binsExpression;
	std::optional<CovergroupRangeList> *covergroupRangeList;
};

class SelectExpression
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<CrossSetExpression, std::optional<IntegerCovergroupExpression>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<CrossIdentifier>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<SelectExpression, WithCovergroupExpression, std::optional<IntegerCovergroupExpression>>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<SelectExpression>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<SelectExpression, SelectExpression>>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<std::tuple<SelectExpression, SelectExpression>>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<SelectCondition>>::type v7;
	typedef boost::mpl::push_front<v7, boost::recursive_wrapper<SelectCondition>>::type v8;
public:
	SelectExpression() { }
	boost::make_variant_over<v8>::type choice;
};

class SeqBlock
{
public:
	SeqBlock() { }
	SeqBlock(std::optional<BlockIdentifier> * _blockIdentifier0, std::vector<BlockItemDeclaration> * _blockItemDeclaration, std::vector<StatementOrNull> * _statementOrNull, std::optional<BlockIdentifier> * _blockIdentifier3) { blockIdentifier0 = _blockIdentifier0; blockItemDeclaration = _blockItemDeclaration; statementOrNull = _statementOrNull; blockIdentifier3 = _blockIdentifier3; }

	std::optional<BlockIdentifier> *blockIdentifier0;
	std::vector<BlockItemDeclaration> *blockItemDeclaration;
	std::vector<StatementOrNull> *statementOrNull;
	std::optional<BlockIdentifier> *blockIdentifier3;
};

class SeqInputList
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<EdgeInputList>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<LevelInputList>>::type v2;
public:
	SeqInputList() { }
	boost::make_variant_over<v2>::type choice;
};

class SequenceAbbrev
{
public:
	SequenceAbbrev() { }
	SequenceAbbrev(ConsecutiveRepetition * _consecutiveRepetition) { consecutiveRepetition = _consecutiveRepetition; }

	ConsecutiveRepetition *consecutiveRepetition;
};
class SequenceActualArg
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<SequenceExpr>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<EventExpression>>::type v2;
public:
	SequenceActualArg() { }
	boost::make_variant_over<v2>::type choice;
};

class SequenceDeclaration
{
public:
	SequenceDeclaration() { }
	SequenceDeclaration(SequenceIdentifier * _sequenceIdentifier0, std::optional<std::optional<SequencePortList>> * _sequencePortList, std::vector<AssertionVariableDeclaration> * _assertionVariableDeclaration, SequenceExpr * _sequenceExpr, std::optional<SequenceIdentifier> * _sequenceIdentifier4) { sequenceIdentifier0 = _sequenceIdentifier0; sequencePortList = _sequencePortList; assertionVariableDeclaration = _assertionVariableDeclaration; sequenceExpr = _sequenceExpr; sequenceIdentifier4 = _sequenceIdentifier4; }

	SequenceIdentifier *sequenceIdentifier0;
	std::optional<std::optional<SequencePortList>> *sequencePortList;
	std::vector<AssertionVariableDeclaration> *assertionVariableDeclaration;
	SequenceExpr *sequenceExpr;
	std::optional<SequenceIdentifier> *sequenceIdentifier4;
};

class SequenceExpr
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<ClockingEvent, SequenceExpr>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<SequenceExpr, SequenceExpr>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<ExpressionOrDist, SequenceExpr>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<SequenceExpr, std::optional<std::vector<SequenceMatchItem>>>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<SequenceExpr, SequenceExpr>>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<std::tuple<SequenceExpr, SequenceExpr>>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<std::tuple<SequenceExpr, SequenceExpr>>>::type v7;
	typedef boost::mpl::push_front<v7, boost::recursive_wrapper<std::tuple<SequenceExpr, std::optional<std::vector<SequenceMatchItem>>, std::optional<SequenceAbbrev>>>>::type v8;
	typedef boost::mpl::push_front<v8, boost::recursive_wrapper<std::tuple<SequenceInstance, std::optional<SequenceAbbrev>>>>::type v9;
	typedef boost::mpl::push_front<v9, boost::recursive_wrapper<std::tuple<ExpressionOrDist, std::optional<BooleanAbbrev>>>>::type v10;
	typedef boost::mpl::push_front<v10, boost::recursive_wrapper<std::tuple<std::optional<SequenceExpr>, std::vector<std::tuple<CycleDelayRange, SequenceExpr>>>>>::type v11;
public:
	SequenceExpr() { }
	boost::make_variant_over<v11>::type choice;
};

class SequenceFormalType
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<DataTypeOrImplicit>>::type v1;
public:
	SequenceFormalType() { }
	boost::make_variant_over<v1>::type choice;
};

class SequenceIdentifier
{
public:
	SequenceIdentifier() { }
	SequenceIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class SequenceInstance
{
public:
	SequenceInstance() { }
	SequenceInstance(PsOrHierarchicalSequenceIdentifier * _psOrHierarchicalSequenceIdentifier, std::optional<SequenceListOfArguments> * _sequenceListOfArguments) { psOrHierarchicalSequenceIdentifier = _psOrHierarchicalSequenceIdentifier; sequenceListOfArguments = _sequenceListOfArguments; }

	PsOrHierarchicalSequenceIdentifier *psOrHierarchicalSequenceIdentifier;
	std::optional<SequenceListOfArguments> *sequenceListOfArguments;
};

class SequenceListOfArguments
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::vector<std::tuple<Identifier, std::optional<SequenceActualArg>>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<std::optional<SequenceActualArg>>, std::optional<std::vector<std::tuple<Identifier, std::optional<SequenceActualArg>>>>>>>::type v2;
public:
	SequenceListOfArguments() { }
	boost::make_variant_over<v2>::type choice;
};

enum class SequenceLvarPortDirection
{
	Input, Inout, Output
};

class SequenceMatchItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<SubroutineCall>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<IncOrDecExpression>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<OperatorAssignment>>::type v3;
public:
	SequenceMatchItem() { }
	boost::make_variant_over<v3>::type choice;
};

class SequenceMethodCall
{
public:
	SequenceMethodCall() { }
	SequenceMethodCall(SequenceInstance * _sequenceInstance, MethodIdentifier * _methodIdentifier) { sequenceInstance = _sequenceInstance; methodIdentifier = _methodIdentifier; }

	SequenceInstance *sequenceInstance;
	MethodIdentifier *methodIdentifier;
};

class SequencePortItem
{
public:
	SequencePortItem() { }
	SequencePortItem(std::vector<AttributeInstance> * _attributeInstance, std::optional<std::optional<SequenceLvarPortDirection>> * _sequenceLvarPortDirection, SequenceFormalType * _sequenceFormalType, FormalPortIdentifier * _formalPortIdentifier, std::vector<VariableDimension> * _variableDimension, std::optional<SequenceActualArg> * _sequenceActualArg) { attributeInstance = _attributeInstance; sequenceLvarPortDirection = _sequenceLvarPortDirection; sequenceFormalType = _sequenceFormalType; formalPortIdentifier = _formalPortIdentifier; variableDimension = _variableDimension; sequenceActualArg = _sequenceActualArg; }

	std::vector<AttributeInstance> *attributeInstance;
	std::optional<std::optional<SequenceLvarPortDirection>> *sequenceLvarPortDirection;
	SequenceFormalType *sequenceFormalType;
	FormalPortIdentifier *formalPortIdentifier;
	std::vector<VariableDimension> *variableDimension;
	std::optional<SequenceActualArg> *sequenceActualArg;
};

class SequencePortList
{
public:
	SequencePortList() { }
	SequencePortList(SequencePortItem * _sequencePortItem) { sequencePortItem = _sequencePortItem; }

	SequencePortItem *sequencePortItem;
};
class SequentialBody
{
public:
	SequentialBody() { }
	SequentialBody(std::optional<UdpInitialStatement> * _udpInitialStatement, std::vector<SequentialEntry> * _sequentialEntry) { udpInitialStatement = _udpInitialStatement; sequentialEntry = _sequentialEntry; }

	std::optional<UdpInitialStatement> *udpInitialStatement;
	std::vector<SequentialEntry> *sequentialEntry;
};

class SequentialEntry
{
public:
	SequentialEntry() { }
	SequentialEntry(SeqInputList * _seqInputList, CurrentState * _currentState, NextState * _nextState) { seqInputList = _seqInputList; currentState = _currentState; nextState = _nextState; }

	SeqInputList *seqInputList;
	CurrentState *currentState;
	NextState *nextState;
};

class SetCovergroupExpression
{
public:
	SetCovergroupExpression() { }
	SetCovergroupExpression(CovergroupExpression * _covergroupExpression) { covergroupExpression = _covergroupExpression; }

	CovergroupExpression *covergroupExpression;
};
class SetupTimingCheck
{
public:
	SetupTimingCheck() { }
	SetupTimingCheck(DataEvent * _dataEvent, ReferenceEvent * _referenceEvent, TimingCheckLimit * _timingCheckLimit, std::optional<std::optional<Notifier>> * _notifier) { dataEvent = _dataEvent; referenceEvent = _referenceEvent; timingCheckLimit = _timingCheckLimit; notifier = _notifier; }

	DataEvent *dataEvent;
	ReferenceEvent *referenceEvent;
	TimingCheckLimit *timingCheckLimit;
	std::optional<std::optional<Notifier>> *notifier;
};

class SetupholdTimingCheck
{
public:
	SetupholdTimingCheck() { }
	SetupholdTimingCheck(ReferenceEvent * _referenceEvent, DataEvent * _dataEvent, TimingCheckLimit * _timingCheckLimit2, TimingCheckLimit * _timingCheckLimit3, std::optional<std::tuple<std::optional<Notifier>, std::optional<std::tuple<std::optional<TimestampCondition>, std::optional<std::tuple<std::optional<TimecheckCondition>, std::optional<std::tuple<std::optional<DelayedReference>, std::optional<std::optional<DelayedData>>>>>>>>>> * _notifier) { referenceEvent = _referenceEvent; dataEvent = _dataEvent; timingCheckLimit2 = _timingCheckLimit2; timingCheckLimit3 = _timingCheckLimit3; notifier = _notifier; }

	ReferenceEvent *referenceEvent;
	DataEvent *dataEvent;
	TimingCheckLimit *timingCheckLimit2;
	TimingCheckLimit *timingCheckLimit3;
	std::optional<std::tuple<std::optional<Notifier>, std::optional<std::tuple<std::optional<TimestampCondition>, std::optional<std::tuple<std::optional<TimecheckCondition>, std::optional<std::tuple<std::optional<DelayedReference>, std::optional<std::optional<DelayedData>>>>>>>>>> *notifier;
};

class ShowcancelledDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ListOfPathOutputs>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ListOfPathOutputs>>::type v2;
public:
	ShowcancelledDeclaration() { }
	boost::make_variant_over<v2>::type choice;
};

enum class Sign
{
	Plus, Minus
};

class SignalIdentifier
{
public:
	SignalIdentifier() { }
	SignalIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
enum class Signing
{
	Signed, Unsigned
};

class SimpleImmediateAssertStatement
{
public:
	SimpleImmediateAssertStatement() { }
	SimpleImmediateAssertStatement(Expression * _expression, ActionBlock * _actionBlock) { expression = _expression; actionBlock = _actionBlock; }

	Expression *expression;
	ActionBlock *actionBlock;
};

class SimpleImmediateAssertionStatement
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<SimpleImmediateCoverStatement>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<SimpleImmediateAssumeStatement>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<SimpleImmediateAssertStatement>>::type v3;
public:
	SimpleImmediateAssertionStatement() { }
	boost::make_variant_over<v3>::type choice;
};

class SimpleImmediateAssumeStatement
{
public:
	SimpleImmediateAssumeStatement() { }
	SimpleImmediateAssumeStatement(Expression * _expression, ActionBlock * _actionBlock) { expression = _expression; actionBlock = _actionBlock; }

	Expression *expression;
	ActionBlock *actionBlock;
};

class SimpleImmediateCoverStatement
{
public:
	SimpleImmediateCoverStatement() { }
	SimpleImmediateCoverStatement(Expression * _expression, StatementOrNull * _statementOrNull) { expression = _expression; statementOrNull = _statementOrNull; }

	Expression *expression;
	StatementOrNull *statementOrNull;
};

class SimplePathDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<FullPathDescription, PathDelayValue>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<ParallelPathDescription, PathDelayValue>>>::type v2;
public:
	SimplePathDeclaration() { }
	boost::make_variant_over<v2>::type choice;
};

class SimpleType
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<PsParameterIdentifier>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<PsTypeIdentifier>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<NonIntegerType>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<IntegerType>>::type v4;
public:
	SimpleType() { }
	boost::make_variant_over<v4>::type choice;
};

class Size
{
public:
	Size() { }
	Size(UnsignedNumber * _unsignedNumber) { unsignedNumber = _unsignedNumber; }

	UnsignedNumber *unsignedNumber;
};
class SkewTimingCheck
{
public:
	SkewTimingCheck() { }
	SkewTimingCheck(ReferenceEvent * _referenceEvent, DataEvent * _dataEvent, TimingCheckLimit * _timingCheckLimit, std::optional<std::optional<Notifier>> * _notifier) { referenceEvent = _referenceEvent; dataEvent = _dataEvent; timingCheckLimit = _timingCheckLimit; notifier = _notifier; }

	ReferenceEvent *referenceEvent;
	DataEvent *dataEvent;
	TimingCheckLimit *timingCheckLimit;
	std::optional<std::optional<Notifier>> *notifier;
};

class SliceSize
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ConstantExpression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<SimpleType>>::type v2;
public:
	SliceSize() { }
	boost::make_variant_over<v2>::type choice;
};

class SolveBeforeList
{
public:
	SolveBeforeList() { }
	SolveBeforeList(ConstraintPrimary * _constraintPrimary) { constraintPrimary = _constraintPrimary; }

	ConstraintPrimary *constraintPrimary;
};
class SourceText
{
public:
	SourceText() { }
	SourceText(std::optional<TimeunitsDeclaration> * _timeunitsDeclaration, std::vector<Description> * _description) { timeunitsDeclaration = _timeunitsDeclaration; description = _description; }

	std::optional<TimeunitsDeclaration> *timeunitsDeclaration;
	std::vector<Description> *description;
};

class SpecifyBlock
{
public:
	SpecifyBlock() { }
	SpecifyBlock(std::vector<SpecifyItem> * _specifyItem) { specifyItem = _specifyItem; }

	std::vector<SpecifyItem> *specifyItem;
};

class SpecifyInputTerminalDescriptor
{
public:
	SpecifyInputTerminalDescriptor() { }
	SpecifyInputTerminalDescriptor(InputIdentifier * _inputIdentifier, std::optional<ConstantRangeExpression> * _constantRangeExpression) { inputIdentifier = _inputIdentifier; constantRangeExpression = _constantRangeExpression; }

	InputIdentifier *inputIdentifier;
	std::optional<ConstantRangeExpression> *constantRangeExpression;
};

class SpecifyItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<SystemTimingCheck>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<PathDeclaration>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<ShowcancelledDeclaration>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<PulsestyleDeclaration>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<SpecparamDeclaration>>::type v5;
public:
	SpecifyItem() { }
	boost::make_variant_over<v5>::type choice;
};

class SpecifyOutputTerminalDescriptor
{
public:
	SpecifyOutputTerminalDescriptor() { }
	SpecifyOutputTerminalDescriptor(OutputIdentifier * _outputIdentifier, std::optional<ConstantRangeExpression> * _constantRangeExpression) { outputIdentifier = _outputIdentifier; constantRangeExpression = _constantRangeExpression; }

	OutputIdentifier *outputIdentifier;
	std::optional<ConstantRangeExpression> *constantRangeExpression;
};

class SpecifyTerminalDescriptor
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<SpecifyOutputTerminalDescriptor>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<SpecifyInputTerminalDescriptor>>::type v2;
public:
	SpecifyTerminalDescriptor() { }
	boost::make_variant_over<v2>::type choice;
};

class SpecparamAssignment
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<PulseControlSpecparam>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<SpecparamIdentifier, ConstantMintypmaxExpression>>>::type v2;
public:
	SpecparamAssignment() { }
	boost::make_variant_over<v2>::type choice;
};

class SpecparamDeclaration
{
public:
	SpecparamDeclaration() { }
	SpecparamDeclaration(std::optional<PackedDimension> * _packedDimension, ListOfSpecparamAssignments * _listOfSpecparamAssignments) { packedDimension = _packedDimension; listOfSpecparamAssignments = _listOfSpecparamAssignments; }

	std::optional<PackedDimension> *packedDimension;
	ListOfSpecparamAssignments *listOfSpecparamAssignments;
};

class SpecparamIdentifier
{
public:
	SpecparamIdentifier() { }
	SpecparamIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class StartEdgeOffset
{
public:
	StartEdgeOffset() { }
	StartEdgeOffset(MintypmaxExpression * _mintypmaxExpression) { mintypmaxExpression = _mintypmaxExpression; }

	MintypmaxExpression *mintypmaxExpression;
};
class StateDependentPathDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<SimplePathDeclaration>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<ModulePathExpression, EdgeSensitivePathDeclaration>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<ModulePathExpression, SimplePathDeclaration>>>::type v3;
public:
	StateDependentPathDeclaration() { }
	boost::make_variant_over<v3>::type choice;
};

class Statement
{
public:
	Statement() { }
	Statement(std::optional<BlockIdentifier> * _blockIdentifier, std::vector<AttributeInstance> * _attributeInstance, StatementItem * _statementItem) { blockIdentifier = _blockIdentifier; attributeInstance = _attributeInstance; statementItem = _statementItem; }

	std::optional<BlockIdentifier> *blockIdentifier;
	std::vector<AttributeInstance> *attributeInstance;
	StatementItem *statementItem;
};

class StatementItem
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ExpectPropertyStatement>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<RandcaseStatement>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<RandsequenceStatement>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<ClockingDrive>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<ProceduralAssertionStatement>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<WaitStatement>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<SeqBlock>>::type v7;
	typedef boost::mpl::push_front<v7, boost::recursive_wrapper<ProceduralTimingControlStatement>>::type v8;
	typedef boost::mpl::push_front<v8, boost::recursive_wrapper<ParBlock>>::type v9;
	typedef boost::mpl::push_front<v9, boost::recursive_wrapper<JumpStatement>>::type v10;
	typedef boost::mpl::push_front<v10, boost::recursive_wrapper<LoopStatement>>::type v11;
	typedef boost::mpl::push_front<v11, boost::recursive_wrapper<EventTrigger>>::type v12;
	typedef boost::mpl::push_front<v12, boost::recursive_wrapper<DisableStatement>>::type v13;
	typedef boost::mpl::push_front<v13, boost::recursive_wrapper<SubroutineCallStatement>>::type v14;
	typedef boost::mpl::push_front<v14, boost::recursive_wrapper<IncOrDecExpression>>::type v15;
	typedef boost::mpl::push_front<v15, boost::recursive_wrapper<ConditionalStatement>>::type v16;
	typedef boost::mpl::push_front<v16, boost::recursive_wrapper<CaseStatement>>::type v17;
	typedef boost::mpl::push_front<v17, boost::recursive_wrapper<ProceduralContinuousAssignment>>::type v18;
	typedef boost::mpl::push_front<v18, boost::recursive_wrapper<NonblockingAssignment>>::type v19;
	typedef boost::mpl::push_front<v19, boost::recursive_wrapper<BlockingAssignment>>::type v20;
public:
	StatementItem() { }
	boost::make_variant_over<v20>::type choice;
};

class StatementOrNull
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::vector<AttributeInstance>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<Statement>>::type v2;
public:
	StatementOrNull() { }
	boost::make_variant_over<v2>::type choice;
};

class StreamConcatenation
{
public:
	StreamConcatenation() { }
	StreamConcatenation(std::vector<StreamExpression> * _streamExpression) { streamExpression = _streamExpression; }

	std::vector<StreamExpression> *streamExpression;
};

class StreamExpression
{
public:
	StreamExpression() { }
	StreamExpression(Expression * _expression, std::optional<ArrayRangeExpression> * _arrayRangeExpression) { expression = _expression; arrayRangeExpression = _arrayRangeExpression; }

	Expression *expression;
	std::optional<ArrayRangeExpression> *arrayRangeExpression;
};

enum class StreamOperator
{
	Gtgt, Ltlt
};

class StreamingConcatenation
{
public:
	StreamingConcatenation() { }
	StreamingConcatenation(StreamOperator * _streamOperator, std::optional<SliceSize> * _sliceSize, StreamConcatenation * _streamConcatenation) { streamOperator = _streamOperator; sliceSize = _sliceSize; streamConcatenation = _streamConcatenation; }

	StreamOperator *streamOperator;
	std::optional<SliceSize> *sliceSize;
	StreamConcatenation *streamConcatenation;
};

enum class Strength0
{
	Supply0, Strong0, Pull0, Weak0, Highz0
};

enum class Strength1
{
	Supply1, Strong1, Pull1, Weak1, Highz1
};

typedef std::string StringLiteral;
enum class StructUnion
{
	Struct
};

class StructUnionMember
{
public:
	StructUnionMember() { }
	StructUnionMember(std::vector<AttributeInstance> * _attributeInstance, std::optional<RandomQualifier> * _randomQualifier, DataTypeOrVoid * _dataTypeOrVoid, ListOfVariableDeclAssignments * _listOfVariableDeclAssignments) { attributeInstance = _attributeInstance; randomQualifier = _randomQualifier; dataTypeOrVoid = _dataTypeOrVoid; listOfVariableDeclAssignments = _listOfVariableDeclAssignments; }

	std::vector<AttributeInstance> *attributeInstance;
	std::optional<RandomQualifier> *randomQualifier;
	DataTypeOrVoid *dataTypeOrVoid;
	ListOfVariableDeclAssignments *listOfVariableDeclAssignments;
};

class StructurePatternKey
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<AssignmentPatternKey>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<MemberIdentifier>>::type v2;
public:
	StructurePatternKey() { }
	boost::make_variant_over<v2>::type choice;
};

class SubroutineCall
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<int>, RandomizeCall>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<MethodCall>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<SystemTfCall>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<TfCall>>::type v4;
public:
	SubroutineCall() { }
	boost::make_variant_over<v4>::type choice;
};

class SubroutineCallStatement
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<FunctionSubroutineCall>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<SubroutineCall>>::type v2;
public:
	SubroutineCallStatement() { }
	boost::make_variant_over<v2>::type choice;
};

class SystemTfCall
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<SystemTfIdentifier, DataType, std::optional<Expression>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<SystemTfIdentifier, std::optional<ListOfArguments>>>>::type v2;
public:
	SystemTfCall() { }
	boost::make_variant_over<v2>::type choice;
};

typedef std::string SystemTfIdentifier;
class SystemTimingCheck
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<NochangeTimingCheck>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<WidthTimingCheck>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<PeriodTimingCheck>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<FullskewTimingCheck>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<TimeskewTimingCheck>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<SkewTimingCheck>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<RecremTimingCheck>>::type v7;
	typedef boost::mpl::push_front<v7, boost::recursive_wrapper<RemovalTimingCheck>>::type v8;
	typedef boost::mpl::push_front<v8, boost::recursive_wrapper<RecoveryTimingCheck>>::type v9;
	typedef boost::mpl::push_front<v9, boost::recursive_wrapper<SetupholdTimingCheck>>::type v10;
	typedef boost::mpl::push_front<v10, boost::recursive_wrapper<HoldTimingCheck>>::type v11;
	typedef boost::mpl::push_front<v11, boost::recursive_wrapper<SetupTimingCheck>>::type v12;
public:
	SystemTimingCheck() { }
	boost::make_variant_over<v12>::type choice;
};

class T01PathDelayExpression
{
public:
	T01PathDelayExpression() { }
	T01PathDelayExpression(PathDelayExpression * _pathDelayExpression) { pathDelayExpression = _pathDelayExpression; }

	PathDelayExpression *pathDelayExpression;
};
class T0xPathDelayExpression
{
public:
	T0xPathDelayExpression() { }
	T0xPathDelayExpression(PathDelayExpression * _pathDelayExpression) { pathDelayExpression = _pathDelayExpression; }

	PathDelayExpression *pathDelayExpression;
};
class T0zPathDelayExpression
{
public:
	T0zPathDelayExpression() { }
	T0zPathDelayExpression(PathDelayExpression * _pathDelayExpression) { pathDelayExpression = _pathDelayExpression; }

	PathDelayExpression *pathDelayExpression;
};
class T10PathDelayExpression
{
public:
	T10PathDelayExpression() { }
	T10PathDelayExpression(PathDelayExpression * _pathDelayExpression) { pathDelayExpression = _pathDelayExpression; }

	PathDelayExpression *pathDelayExpression;
};
class T1xPathDelayExpression
{
public:
	T1xPathDelayExpression() { }
	T1xPathDelayExpression(PathDelayExpression * _pathDelayExpression) { pathDelayExpression = _pathDelayExpression; }

	PathDelayExpression *pathDelayExpression;
};
class T1zPathDelayExpression
{
public:
	T1zPathDelayExpression() { }
	T1zPathDelayExpression(PathDelayExpression * _pathDelayExpression) { pathDelayExpression = _pathDelayExpression; }

	PathDelayExpression *pathDelayExpression;
};
class TPathDelayExpression
{
public:
	TPathDelayExpression() { }
	TPathDelayExpression(PathDelayExpression * _pathDelayExpression) { pathDelayExpression = _pathDelayExpression; }

	PathDelayExpression *pathDelayExpression;
};
class TaggedUnionExpression
{
public:
	TaggedUnionExpression() { }
	TaggedUnionExpression(MemberIdentifier * _memberIdentifier, std::optional<Expression> * _expression) { memberIdentifier = _memberIdentifier; expression = _expression; }

	MemberIdentifier *memberIdentifier;
	std::optional<Expression> *expression;
};

class TaskBodyDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<ClassScope>, TaskIdentifier, std::optional<TfPortList>, std::vector<BlockItemDeclaration>, std::vector<StatementOrNull>, std::optional<TaskIdentifier>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<InterfaceIdentifier>, TaskIdentifier, std::optional<TfPortList>, std::vector<BlockItemDeclaration>, std::vector<StatementOrNull>, std::optional<TaskIdentifier>>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::optional<ClassScope>, TaskIdentifier, std::vector<TfItemDeclaration>, std::vector<StatementOrNull>, std::optional<TaskIdentifier>>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<std::optional<InterfaceIdentifier>, TaskIdentifier, std::vector<TfItemDeclaration>, std::vector<StatementOrNull>, std::optional<TaskIdentifier>>>>::type v4;
public:
	TaskBodyDeclaration() { }
	boost::make_variant_over<v4>::type choice;
};

class TaskDeclaration
{
public:
	TaskDeclaration() { }
	TaskDeclaration(std::optional<Lifetime> * _lifetime, TaskBodyDeclaration * _taskBodyDeclaration) { lifetime = _lifetime; taskBodyDeclaration = _taskBodyDeclaration; }

	std::optional<Lifetime> *lifetime;
	TaskBodyDeclaration *taskBodyDeclaration;
};

class TaskIdentifier
{
public:
	TaskIdentifier() { }
	TaskIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class TaskPrototype
{
public:
	TaskPrototype() { }
	TaskPrototype(TaskIdentifier * _taskIdentifier, std::optional<std::optional<TfPortList>> * _tfPortList) { taskIdentifier = _taskIdentifier; tfPortList = _tfPortList; }

	TaskIdentifier *taskIdentifier;
	std::optional<std::optional<TfPortList>> *tfPortList;
};

class TerminalIdentifier
{
public:
	TerminalIdentifier() { }
	TerminalIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class TfCall
{
public:
	TfCall() { }
	TfCall(PsOrHierarchicalTfIdentifier * _psOrHierarchicalTfIdentifier, std::vector<AttributeInstance> * _attributeInstance, std::optional<ListOfArguments> * _listOfArguments) { psOrHierarchicalTfIdentifier = _psOrHierarchicalTfIdentifier; attributeInstance = _attributeInstance; listOfArguments = _listOfArguments; }

	PsOrHierarchicalTfIdentifier *psOrHierarchicalTfIdentifier;
	std::vector<AttributeInstance> *attributeInstance;
	std::optional<ListOfArguments> *listOfArguments;
};

class TfIdentifier
{
public:
	TfIdentifier() { }
	TfIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class TfItemDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<TfPortDeclaration>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<BlockItemDeclaration>>::type v2;
public:
	TfItemDeclaration() { }
	boost::make_variant_over<v2>::type choice;
};

class TfPortDeclaration
{
public:
	TfPortDeclaration() { }
	TfPortDeclaration(std::vector<AttributeInstance> * _attributeInstance, TfPortDirection * _tfPortDirection, DataTypeOrImplicit * _dataTypeOrImplicit, ListOfTfVariableIdentifiers * _listOfTfVariableIdentifiers) { attributeInstance = _attributeInstance; tfPortDirection = _tfPortDirection; dataTypeOrImplicit = _dataTypeOrImplicit; listOfTfVariableIdentifiers = _listOfTfVariableIdentifiers; }

	std::vector<AttributeInstance> *attributeInstance;
	TfPortDirection *tfPortDirection;
	DataTypeOrImplicit *dataTypeOrImplicit;
	ListOfTfVariableIdentifiers *listOfTfVariableIdentifiers;
};

class TfPortDirection
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<PortDirection>>::type v1;
public:
	TfPortDirection() { }
	boost::make_variant_over<v1>::type choice;
};

class TfPortItem
{
public:
	TfPortItem() { }
	TfPortItem(std::vector<AttributeInstance> * _attributeInstance, std::optional<TfPortDirection> * _tfPortDirection, DataTypeOrImplicit * _dataTypeOrImplicit, std::optional<std::tuple<PortIdentifier, std::vector<VariableDimension>, std::optional<Expression>>> * _portIdentifier) { attributeInstance = _attributeInstance; tfPortDirection = _tfPortDirection; dataTypeOrImplicit = _dataTypeOrImplicit; portIdentifier = _portIdentifier; }

	std::vector<AttributeInstance> *attributeInstance;
	std::optional<TfPortDirection> *tfPortDirection;
	DataTypeOrImplicit *dataTypeOrImplicit;
	std::optional<std::tuple<PortIdentifier, std::vector<VariableDimension>, std::optional<Expression>>> *portIdentifier;
};

class TfPortList
{
public:
	TfPortList() { }
	TfPortList(TfPortItem * _tfPortItem) { tfPortItem = _tfPortItem; }

	TfPortItem *tfPortItem;
};
class TfallPathDelayExpression
{
public:
	TfallPathDelayExpression() { }
	TfallPathDelayExpression(PathDelayExpression * _pathDelayExpression) { pathDelayExpression = _pathDelayExpression; }

	PathDelayExpression *pathDelayExpression;
};
class Threshold
{
public:
	Threshold() { }
	Threshold(ConstantExpression * _constantExpression) { constantExpression = _constantExpression; }

	ConstantExpression *constantExpression;
};
class TimeLiteral
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<FixedPointNumber, TimeUnit>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<UnsignedNumber, TimeUnit>>>::type v2;
public:
	TimeLiteral() { }
	boost::make_variant_over<v2>::type choice;
};

class TimeUnit
{
public:
	TimeUnit() { }
	TimeUnit(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class TimecheckCondition
{
public:
	TimecheckCondition() { }
	TimecheckCondition(MintypmaxExpression * _mintypmaxExpression) { mintypmaxExpression = _mintypmaxExpression; }

	MintypmaxExpression *mintypmaxExpression;
};
class TimeskewTimingCheck
{
public:
	TimeskewTimingCheck() { }
	TimeskewTimingCheck(ReferenceEvent * _referenceEvent, DataEvent * _dataEvent, TimingCheckLimit * _timingCheckLimit, std::optional<std::tuple<std::optional<Notifier>, std::optional<std::tuple<std::optional<EventBasedFlag>, std::optional<std::optional<RemainActiveFlag>>>>>> * _notifier) { referenceEvent = _referenceEvent; dataEvent = _dataEvent; timingCheckLimit = _timingCheckLimit; notifier = _notifier; }

	ReferenceEvent *referenceEvent;
	DataEvent *dataEvent;
	TimingCheckLimit *timingCheckLimit;
	std::optional<std::tuple<std::optional<Notifier>, std::optional<std::tuple<std::optional<EventBasedFlag>, std::optional<std::optional<RemainActiveFlag>>>>>> *notifier;
};

class TimestampCondition
{
public:
	TimestampCondition() { }
	TimestampCondition(MintypmaxExpression * _mintypmaxExpression) { mintypmaxExpression = _mintypmaxExpression; }

	MintypmaxExpression *mintypmaxExpression;
};
class TimeunitsDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<TimeLiteral, TimeLiteral>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<TimeLiteral, TimeLiteral>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<TimeLiteral>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<TimeLiteral, std::optional<TimeLiteral>>>>::type v4;
public:
	TimeunitsDeclaration() { }
	boost::make_variant_over<v4>::type choice;
};

class TimingCheckCondition
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ScalarTimingCheckCondition>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ScalarTimingCheckCondition>>::type v2;
public:
	TimingCheckCondition() { }
	boost::make_variant_over<v2>::type choice;
};

class TimingCheckEvent
{
public:
	TimingCheckEvent() { }
	TimingCheckEvent(std::optional<TimingCheckEventControl> * _timingCheckEventControl, SpecifyTerminalDescriptor * _specifyTerminalDescriptor, std::optional<TimingCheckCondition> * _timingCheckCondition) { timingCheckEventControl = _timingCheckEventControl; specifyTerminalDescriptor = _specifyTerminalDescriptor; timingCheckCondition = _timingCheckCondition; }

	std::optional<TimingCheckEventControl> *timingCheckEventControl;
	SpecifyTerminalDescriptor *specifyTerminalDescriptor;
	std::optional<TimingCheckCondition> *timingCheckCondition;
};

class TimingCheckEventControl
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<EdgeControlSpecifier>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<EdgeIdentifier>>::type v2;
public:
	TimingCheckEventControl() { }
	boost::make_variant_over<v2>::type choice;
};

class TimingCheckLimit
{
public:
	TimingCheckLimit() { }
	TimingCheckLimit(Expression * _expression) { expression = _expression; }

	Expression *expression;
};
class TopmoduleIdentifier
{
public:
	TopmoduleIdentifier() { }
	TopmoduleIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class TransItem
{
public:
	TransItem() { }
	TransItem(CovergroupRangeList * _covergroupRangeList) { covergroupRangeList = _covergroupRangeList; }

	CovergroupRangeList *covergroupRangeList;
};
class TransList
{
public:
	TransList() { }
	TransList(TransSet * _transSet) { transSet = _transSet; }

	TransSet *transSet;
};
class TransRangeList
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<TransItem, RepeatRange>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<TransItem, RepeatRange>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<TransItem, RepeatRange>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<TransItem>>::type v4;
public:
	TransRangeList() { }
	boost::make_variant_over<v4>::type choice;
};

class TransSet
{
public:
	TransSet() { }
	TransSet(TransRangeList * _transRangeList) { transRangeList = _transRangeList; }

	TransRangeList *transRangeList;
};
class TrisePathDelayExpression
{
public:
	TrisePathDelayExpression() { }
	TrisePathDelayExpression(PathDelayExpression * _pathDelayExpression) { pathDelayExpression = _pathDelayExpression; }

	PathDelayExpression *pathDelayExpression;
};
class Tx0PathDelayExpression
{
public:
	Tx0PathDelayExpression() { }
	Tx0PathDelayExpression(PathDelayExpression * _pathDelayExpression) { pathDelayExpression = _pathDelayExpression; }

	PathDelayExpression *pathDelayExpression;
};
class Tx1PathDelayExpression
{
public:
	Tx1PathDelayExpression() { }
	Tx1PathDelayExpression(PathDelayExpression * _pathDelayExpression) { pathDelayExpression = _pathDelayExpression; }

	PathDelayExpression *pathDelayExpression;
};
class TxzPathDelayExpression
{
public:
	TxzPathDelayExpression() { }
	TxzPathDelayExpression(PathDelayExpression * _pathDelayExpression) { pathDelayExpression = _pathDelayExpression; }

	PathDelayExpression *pathDelayExpression;
};
class TypeAssignment
{
public:
	TypeAssignment() { }
	TypeAssignment(TypeIdentifier * _typeIdentifier, std::optional<DataType> * _dataType) { typeIdentifier = _typeIdentifier; dataType = _dataType; }

	TypeIdentifier *typeIdentifier;
	std::optional<DataType> *dataType;
};

class TypeDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<int>, TypeIdentifier>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<TypeIdentifier>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<TypeIdentifier>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<TypeIdentifier>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<TypeIdentifier>>::type v5;
	typedef boost::mpl::push_front<v5, boost::recursive_wrapper<std::tuple<InterfaceIntanceIdentifier, ConstantBitSelect, TypeIdentifier, TypeIdentifier>>>::type v6;
	typedef boost::mpl::push_front<v6, boost::recursive_wrapper<std::tuple<DataType, TypeIdentifier, std::vector<VariableDimension>>>>::type v7;
public:
	TypeDeclaration() { }
	boost::make_variant_over<v7>::type choice;
};

class TypeIdentifier
{
public:
	TypeIdentifier() { }
	TypeIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class TypeReference
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<DataType>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<Expression>>::type v2;
public:
	TypeReference() { }
	boost::make_variant_over<v2>::type choice;
};

class Tz0PathDelayExpression
{
public:
	Tz0PathDelayExpression() { }
	Tz0PathDelayExpression(PathDelayExpression * _pathDelayExpression) { pathDelayExpression = _pathDelayExpression; }

	PathDelayExpression *pathDelayExpression;
};
class Tz1PathDelayExpression
{
public:
	Tz1PathDelayExpression() { }
	Tz1PathDelayExpression(PathDelayExpression * _pathDelayExpression) { pathDelayExpression = _pathDelayExpression; }

	PathDelayExpression *pathDelayExpression;
};
class TzPathDelayExpression
{
public:
	TzPathDelayExpression() { }
	TzPathDelayExpression(PathDelayExpression * _pathDelayExpression) { pathDelayExpression = _pathDelayExpression; }

	PathDelayExpression *pathDelayExpression;
};
class TzxPathDelayExpression
{
public:
	TzxPathDelayExpression() { }
	TzxPathDelayExpression(PathDelayExpression * _pathDelayExpression) { pathDelayExpression = _pathDelayExpression; }

	PathDelayExpression *pathDelayExpression;
};
class UdpAnsiDeclaration
{
public:
	UdpAnsiDeclaration() { }
	UdpAnsiDeclaration(std::vector<AttributeInstance> * _attributeInstance, UdpIdentifier * _udpIdentifier, UdpDeclarationPortList * _udpDeclarationPortList) { attributeInstance = _attributeInstance; udpIdentifier = _udpIdentifier; udpDeclarationPortList = _udpDeclarationPortList; }

	std::vector<AttributeInstance> *attributeInstance;
	UdpIdentifier *udpIdentifier;
	UdpDeclarationPortList *udpDeclarationPortList;
};

class UdpBody
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<SequentialBody>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<CombinationalBody>>::type v2;
public:
	UdpBody() { }
	boost::make_variant_over<v2>::type choice;
};

class UdpDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, UdpIdentifier, std::vector<UdpPortDeclaration>, UdpBody, std::optional<UdpIdentifier>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<UdpAnsiDeclaration>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<UdpNonansiDeclaration>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<UdpAnsiDeclaration, UdpBody, std::optional<UdpIdentifier>>>>::type v4;
	typedef boost::mpl::push_front<v4, boost::recursive_wrapper<std::tuple<UdpNonansiDeclaration, std::vector<UdpPortDeclaration>, UdpBody, std::optional<UdpIdentifier>>>>::type v5;
public:
	UdpDeclaration() { }
	boost::make_variant_over<v5>::type choice;
};

class UdpDeclarationPortList
{
public:
	UdpDeclarationPortList() { }
	UdpDeclarationPortList(UdpOutputDeclaration * _udpOutputDeclaration, std::vector<UdpInputDeclaration> * _udpInputDeclaration) { udpOutputDeclaration = _udpOutputDeclaration; udpInputDeclaration = _udpInputDeclaration; }

	UdpOutputDeclaration *udpOutputDeclaration;
	std::vector<UdpInputDeclaration> *udpInputDeclaration;
};

class UdpIdentifier
{
public:
	UdpIdentifier() { }
	UdpIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class UdpInitialStatement
{
public:
	UdpInitialStatement() { }
	UdpInitialStatement(OutputPortIdentifier * _outputPortIdentifier, InitVal * _initVal) { outputPortIdentifier = _outputPortIdentifier; initVal = _initVal; }

	OutputPortIdentifier *outputPortIdentifier;
	InitVal *initVal;
};

class UdpInputDeclaration
{
public:
	UdpInputDeclaration() { }
	UdpInputDeclaration(std::vector<AttributeInstance> * _attributeInstance, ListOfUdpPortIdentifiers * _listOfUdpPortIdentifiers) { attributeInstance = _attributeInstance; listOfUdpPortIdentifiers = _listOfUdpPortIdentifiers; }

	std::vector<AttributeInstance> *attributeInstance;
	ListOfUdpPortIdentifiers *listOfUdpPortIdentifiers;
};

class UdpInstance
{
public:
	UdpInstance() { }
	UdpInstance(std::optional<NameOfInstance> * _nameOfInstance, OutputTerminal * _outputTerminal, std::vector<InputTerminal> * _inputTerminal) { nameOfInstance = _nameOfInstance; outputTerminal = _outputTerminal; inputTerminal = _inputTerminal; }

	std::optional<NameOfInstance> *nameOfInstance;
	OutputTerminal *outputTerminal;
	std::vector<InputTerminal> *inputTerminal;
};

class UdpInstantiation
{
public:
	UdpInstantiation() { }
	UdpInstantiation(UdpIdentifier * _udpIdentifier, std::optional<DriveStrength> * _driveStrength, std::optional<Delay2> * _delay2, std::vector<UdpInstance> * _udpInstance) { udpIdentifier = _udpIdentifier; driveStrength = _driveStrength; delay2 = _delay2; udpInstance = _udpInstance; }

	UdpIdentifier *udpIdentifier;
	std::optional<DriveStrength> *driveStrength;
	std::optional<Delay2> *delay2;
	std::vector<UdpInstance> *udpInstance;
};

class UdpNonansiDeclaration
{
public:
	UdpNonansiDeclaration() { }
	UdpNonansiDeclaration(std::vector<AttributeInstance> * _attributeInstance, UdpIdentifier * _udpIdentifier, UdpPortList * _udpPortList) { attributeInstance = _attributeInstance; udpIdentifier = _udpIdentifier; udpPortList = _udpPortList; }

	std::vector<AttributeInstance> *attributeInstance;
	UdpIdentifier *udpIdentifier;
	UdpPortList *udpPortList;
};

class UdpOutputDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, PortIdentifier, std::optional<ConstantExpression>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<AttributeInstance>, PortIdentifier>>>::type v2;
public:
	UdpOutputDeclaration() { }
	boost::make_variant_over<v2>::type choice;
};

class UdpPortDeclaration
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<UdpRegDeclaration>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<UdpInputDeclaration>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<UdpOutputDeclaration>>::type v3;
public:
	UdpPortDeclaration() { }
	boost::make_variant_over<v3>::type choice;
};

class UdpPortList
{
public:
	UdpPortList() { }
	UdpPortList(OutputPortIdentifier * _outputPortIdentifier, std::vector<InputPortIdentifier> * _inputPortIdentifier) { outputPortIdentifier = _outputPortIdentifier; inputPortIdentifier = _inputPortIdentifier; }

	OutputPortIdentifier *outputPortIdentifier;
	std::vector<InputPortIdentifier> *inputPortIdentifier;
};

class UdpRegDeclaration
{
public:
	UdpRegDeclaration() { }
	UdpRegDeclaration(std::vector<AttributeInstance> * _attributeInstance, VariableIdentifier * _variableIdentifier) { attributeInstance = _attributeInstance; variableIdentifier = _variableIdentifier; }

	std::vector<AttributeInstance> *attributeInstance;
	VariableIdentifier *variableIdentifier;
};

enum class UnaryModulePathOperator
{
	Notop, Amp, Pipe, Tilde, Caret
};

enum class UnaryOperator
{
	Notop, Amp, Pipe, Tilde, Caret
};

class UnbasedUnsizedLiteral
{
public:
	UnbasedUnsizedLiteral() { }
	UnbasedUnsizedLiteral(UnsignedNumber * _unsignedNumber) { unsignedNumber = _unsignedNumber; }

	UnsignedNumber *unsignedNumber;
};

enum class UniquePriority
{
	Unique, Unique0, Priority
};

class UniquenessConstraint
{
public:
	UniquenessConstraint() { }
	UniquenessConstraint(std::vector<OpenRangeList> * _openRangeList) { openRangeList = _openRangeList; }

	std::vector<OpenRangeList> *openRangeList;
};

class UnpackedDimension
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<ConstantExpression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<ConstantRange>>::type v2;
public:
	UnpackedDimension() { }
	boost::make_variant_over<v2>::type choice;
};

typedef std::string UnsignedNumber;
enum class UnsizedDimension
{
	Lbracket, Rbracket
};

class UseClause
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::optional<LibraryIdentifier>, CellIdentifier, std::vector<NamedParameterAssignment>, std::optional<int>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::vector<NamedParameterAssignment>, std::optional<int>>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<std::optional<LibraryIdentifier>, CellIdentifier, std::optional<int>>>>::type v3;
public:
	UseClause() { }
	boost::make_variant_over<v3>::type choice;
};

class ValueRange
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<Expression, Expression>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<Expression>>::type v2;
public:
	ValueRange() { }
	boost::make_variant_over<v2>::type choice;
};

class VarDataType
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<DataTypeOrImplicit>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<DataType>>::type v2;
public:
	VarDataType() { }
	boost::make_variant_over<v2>::type choice;
};

class VariableAssignment
{
public:
	VariableAssignment() { }
	VariableAssignment(VariableLvalue * _variableLvalue, Expression * _expression) { variableLvalue = _variableLvalue; expression = _expression; }

	VariableLvalue *variableLvalue;
	Expression *expression;
};

class VariableDeclAssignment
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<ClassVariableIdentifier, std::optional<ClassNew>>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<DynamicArrayVariableIdentifier, UnsizedDimension, std::vector<VariableDimension>, std::optional<DynamicArrayNew>>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::tuple<VariableIdentifier, std::vector<VariableDimension>, std::optional<Expression>>>>::type v3;
public:
	VariableDeclAssignment() { }
	boost::make_variant_over<v3>::type choice;
};

class VariableDimension
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<QueueDimension>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<AssociativeDimension>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<UnpackedDimension>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<UnsizedDimension>>::type v4;
public:
	VariableDimension() { }
	boost::make_variant_over<v4>::type choice;
};

class VariableIdentifier
{
public:
	VariableIdentifier() { }
	VariableIdentifier(Identifier * _identifier) { identifier = _identifier; }

	Identifier *identifier;
};
class VariableIdentifierList
{
public:
	VariableIdentifierList() { }
	VariableIdentifierList(VariableIdentifier * _variableIdentifier) { variableIdentifier = _variableIdentifier; }

	VariableIdentifier *variableIdentifier;
};
class VariableLvalue
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<StreamingConcatenation>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<std::optional<AssignmentPatternExpressionType>, AssignmentPatternVariableLvalue>>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<std::vector<VariableLvalue>>>::type v3;
	typedef boost::mpl::push_front<v3, boost::recursive_wrapper<std::tuple<HierarchicalVariableIdentifier, Select>>>::type v4;
public:
	VariableLvalue() { }
	boost::make_variant_over<v4>::type choice;
};

class VariablePortHeader
{
public:
	VariablePortHeader() { }
	VariablePortHeader(std::optional<PortDirection> * _portDirection, VariablePortType * _variablePortType) { portDirection = _portDirection; variablePortType = _variablePortType; }

	std::optional<PortDirection> *portDirection;
	VariablePortType *variablePortType;
};

class VariablePortType
{
public:
	VariablePortType() { }
	VariablePortType(VarDataType * _varDataType) { varDataType = _varDataType; }

	VarDataType *varDataType;
};
class WaitStatement
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<std::tuple<std::vector<HierarchicalIdentifier>, ActionBlock>>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<std::tuple<Expression, StatementOrNull>>>::type v2;
public:
	WaitStatement() { }
	boost::make_variant_over<v2>::type choice;
};

class WeightSpecification
{
	typedef boost::mpl::vector<> v0;
	typedef boost::mpl::push_front<v0, boost::recursive_wrapper<Expression>>::type v1;
	typedef boost::mpl::push_front<v1, boost::recursive_wrapper<PsIdentifier>>::type v2;
	typedef boost::mpl::push_front<v2, boost::recursive_wrapper<IntegralNumber>>::type v3;
public:
	WeightSpecification() { }
	boost::make_variant_over<v3>::type choice;
};

class WidthTimingCheck
{
public:
	WidthTimingCheck() { }
	WidthTimingCheck(ControlledReferenceEvent * _controlledReferenceEvent, TimingCheckLimit * _timingCheckLimit, Threshold * _threshold, std::optional<std::optional<Notifier>> * _notifier) { controlledReferenceEvent = _controlledReferenceEvent; timingCheckLimit = _timingCheckLimit; threshold = _threshold; notifier = _notifier; }

	ControlledReferenceEvent *controlledReferenceEvent;
	TimingCheckLimit *timingCheckLimit;
	Threshold *threshold;
	std::optional<std::optional<Notifier>> *notifier;
};

class WithCovergroupExpression
{
public:
	WithCovergroupExpression() { }
	WithCovergroupExpression(CovergroupExpression * _covergroupExpression) { covergroupExpression = _covergroupExpression; }

	CovergroupExpression *covergroupExpression;
};
