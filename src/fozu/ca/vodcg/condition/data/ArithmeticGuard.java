package fozu.ca.vodcg.condition.data;

import java.util.Collection;
import java.util.EnumMap;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Supplier;

import fozu.ca.Mappable;
import fozu.ca.vodcg.VODCondGen;
import fozu.ca.vodcg.condition.Arithmetic;
import fozu.ca.vodcg.condition.ArithmeticExpression;
import fozu.ca.vodcg.condition.Expression;
import fozu.ca.vodcg.condition.Function;
import fozu.ca.vodcg.condition.Function.Parameter;
import fozu.ca.vodcg.condition.FunctionCall;
import fozu.ca.vodcg.condition.Proposition;
import fozu.ca.vodcg.condition.Relation;

/**
 * A wrapper proposition of {@link Arithmetic}.
 * 
 * @author Kao, Chen-yi
 *
 */
public abstract class ArithmeticGuard 
// extensible for all of unary, binary and n-ary guards
extends Proposition 	
implements NumericExpression {

	public enum Operator implements Relation.Operator {
		PRIMITIVE,	// for unary, expression-range guards
		ADD, SUBTRACT, MULTIPLY, DIVIDE, MODULO, MAX, MIN;
		
		@Override
		public boolean isAssociativeTo(Relation.Operator op) {
			return false;
		}
		@Override
		public boolean isCommutative() {
			return Enum.valueOf(Arithmetic.Operator.class, name()).isCommutative();
		}
		
		@Override
		public <M extends Map<?,?>> EnumMap<? extends Key, M> createPartitionMap() {
			return new EnumMap<>(Operator.class);
		}
		
		@Override
		public <M extends Mappable<?, ?>> EnumMap<? extends Key, M> createPartitionMappable() {
			return new EnumMap<>(Operator.class);
		}
		
		
		
		@Override
		public fozu.ca.vodcg.condition.Relation.Operator negate() {
			switch (this) {
			case ADD:			return SUBTRACT;
			case SUBTRACT:		return ADD;
			case MULTIPLY:		return DIVIDE;
			case DIVIDE:		return MULTIPLY;
			case MODULO:		
			default:			return null;
			}
		}
		
		@Override
		public java.lang.String toString() {
			switch (this) {
			case ADD:			return "+guard";
			case SUBTRACT:		return "-guard";
			case MULTIPLY:		return "*guard";
			case DIVIDE:		return "/guard";
			case MODULO:		return "%guard";
//			case Remainder:		return "...guard";
			default:
				assert(false); return null;	// should NOT come here!
			}
		}
		
		public <H extends Relation> java.lang.String toZ3SmtString(
				H host, boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
			switch (this) {
			case ADD:			return "add_guard";
			case SUBTRACT:		return "sub_guard";
			case MULTIPLY:		return "mul_guard";
			case DIVIDE:		return "div_guard";
			case MODULO:		return "mod_guard";
//			case Remainder:		return "rem_guard";
			default:
				assert(false); return null;	// should NOT come here!
			}
		}
		
	}
	
	
	
//	private final static Method METHOD_FROM = Elemental.getMethod(FiniteIntegerGuard.class, 
//			"from", Arithmetic.class);

	private static final Map<ArithmeticExpression, ArithmeticGuard> 
	GUARD_REGISTRY = new HashMap<>();

	/**
	 * @param arith - arithmetic to guard
	 */
	protected ArithmeticGuard(final Arithmetic arith) {
		super(getOp(arith), arith);
	}
	
	/**
	 * @param unit - arithmetic unit to guard
	 */
	protected ArithmeticGuard(final ArithmeticExpression unit) {
		super(Operator.PRIMITIVE, (Expression) unit);
	}
	
	@SuppressWarnings({ "removal" })
	protected static ArithmeticGuard from(
			final ArithmeticExpression ae, final Supplier<ArithmeticGuard> gs) {
		assert gs != null;
		if (ae == null) throwNullArithmeticExpressionException();
		
		ArithmeticGuard g = GUARD_REGISTRY.get(ae);
		if (g == null) try {
			g = gs.get();
			GUARD_REGISTRY.put(ae, g);
//			GUARD_REGISTRY.put(ae, g = arith.guardReenter(
//					()-> new FiniteIntegerGuard(arith), ()-> throwStackOverflowException(), METHOD_FROM));
			
		} catch (Exception e) {
			throwUnhandledException(e);
		}
		return g;
	}

	/**
	 * @return
	 */
	private static ArithmeticGuard throwNullArithmeticExpressionException() {
		return throwNullArgumentException("arithmetic");
	}
	
	public static ArithmeticGuard from(final Arithmetic arith) {
		if (arith == null) throwNullArithmeticExpressionException();
		return arith.getOp().isBitwise()
				? BitsGuard.from(arith)
				: FiniteNumberGuard.from(arith);
	}
	

	
	private static java.lang.String getName(Arithmetic arith) {
		if (arith == null) throwNullArithmeticExpressionException();
		return getOp(arith).toZ3SmtString(null, false, false);
	}
	
	@SuppressWarnings("removal")
	private static Relation.Operator getOp(Arithmetic arith) {
		assert arith != null;
//		if (arith.getFirstOperand().getType() != DataType.Int)
//			throwTodoException("non-integer guard");
		
		switch ((Arithmetic.Operator) arith.getOp()) {
		case Add:					return ArithmeticGuard.Operator.ADD;
		case Subtract:				return ArithmeticGuard.Operator.SUBTRACT;
		case Multiply:				return ArithmeticGuard.Operator.MULTIPLY;
		case Divide, IntegerDivide:	return ArithmeticGuard.Operator.DIVIDE;
		case Modulo:				return ArithmeticGuard.Operator.MODULO;

		case BitAnd:				return BitsGuard.Operator.BIT_AND;
		default:
		}
		return throwTodoException("unsupported arithmetic");
	}
	
	
	
//	@SuppressWarnings("unchecked")
//	@Override
//	public Operator getOp() {
//		final Expression oprd = getFirstRawOperand();
////		if (oprd.isUnary()) return Operator.PRIMITIVE;
//		
//		if (oprd instanceof Arithmetic) 
//		switch ((Arithmetic.Operator) ((Arithmetic) oprd).getOp()) {
//		case ADD:			return Operator.ADD;
//		case SUBTRACT:		return Operator.SUBTRACT;
//		case DIVIDE:
//		case IntegerDivide:	return Operator.DIVIDE;
//		case MAX:			return Operator.MAX;
//		case MIN:			return Operator.MIN;
//		case MODULO:		return Operator.MODULO;
//		case MULTIPLY:		return Operator.MULTIPLY;
//		case BIT_AND:
//		case ShiftLeft:
//		default:			
//		}
//		return throwTodoException("unsupported op");
//	}
	
	
	
	@Override
	public Collection<? extends Expression> getOperands() {
		final Expression oprd = getFirstRawOperand();
		return oprd instanceof Arithmetic
				? ((Arithmetic) oprd).getOperands()
				: super.getOperands();
	}
	
	/**
	 * One level guarding and no side-effect for the guard.
	 */
	@Override
	protected <O extends Expression> boolean cacheOperandDirectSideEffect(
			final O oprd) {
		return false;
	}
	
//	/**
//	 * One level guarding only - no guards for the guard.
//	 */
//	@Override
//	protected final Set<ArithmeticGuard> cacheArithmeticGuards() {
//		return null;
//	}
	
	
	
	@Override
	public boolean isGuard() {
		return true;
	}

	
	
	@Override
	public Proposition toProposition() {
		final Arithmetic arith = get(()-> (Arithmetic) getFirstRawOperand(),
				e-> throwTodoException(e));
		final java.lang.String name = getName(arith);
		final List<? extends Expression> args = arith.toList();
		return FunctionCall.from(
				Function.from(VODCondGen.LIB_OMPCA_SMT, 
						name, 
						DataType.Bool, 
						arith.getCondGen(),
						Parameter.from(args)),
				name,
				args,
				arith.getScope()).getCallProposition();
	}
	
	@Override
	public java.lang.String toZ3SmtString(
			boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
		return toProposition().toZ3SmtString(
				printsVariableDeclaration, printsFunctionDefinition, isLhs);
	}
	
}