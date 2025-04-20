/**
 * 
 */
package fozu.ca.vodcg.condition.data;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Supplier;

import fozu.ca.DebugElement;
import fozu.ca.Elemental;
import fozu.ca.vodcg.ReenterException;
import fozu.ca.vodcg.SystemElement;
import fozu.ca.vodcg.condition.ConditionElement;
import fozu.ca.vodcg.condition.Equality;
import fozu.ca.vodcg.condition.Expression;
import fozu.ca.vodcg.condition.OrderRelation;
import fozu.ca.vodcg.condition.PathVariablePlaceholder;
import fozu.ca.vodcg.condition.Proposition;
import fozu.ca.vodcg.condition.Proposition.False;
import fozu.ca.vodcg.condition.Proposition.True;
import fozu.ca.vodcg.condition.version.Version;
import fozu.ca.vodcg.util.JavaUtil;

/**
 * @author Kao, Chen-yi
 *
 */
public interface NumericExpression {

	/**
	 * Simplifying to {@link Proposition#True}/{@link Proposition#False} 
	 * if ALL operands are number constants.
	 *  
	 * @param op
	 * @param lhs - assumed of ordered type in the number theory
	 * @param rhs - assumed of ordered type in the number theory
	 * @return
	 */
	public static Proposition from(
			OrderRelation.Operator op, NumericExpression lhs, NumericExpression rhs) {
		if (op == null) Elemental.throwNullArgumentException("operator");
		if (lhs == null) Elemental.throwNullArgumentException("lhs");
		if (rhs == null) Elemental.throwNullArgumentException("rhs");
		
		Boolean isTF = null;
		try { 
//			final Boolean ler = lhs.equals(rhs), lltr = lhs.isLessThan(rhs), 
//					ller = lhs.isLessEqual(rhs);
			switch (op) {
			case Equal:			isTF = lhs.equals(rhs);			break;	// lhs == rhs, NOT lhs = rhs
			case NotEqual:		isTF = !lhs.equals(rhs);		break;	// lhs != rhs
			case GreaterEqual:	isTF = !lhs.isLessThan(rhs);	break;	// lhs >= rhs
			case LessEqual:		isTF = lhs.isLessEqual(rhs);	break;	// lhs <= rhs
			case GreaterThan:	isTF = !lhs.isLessEqual(rhs);	break;	// lhs > rhs
			case LessThan:		isTF = lhs.isLessThan(rhs);		break;	// lhs < rhs
			}
			final Expression le = (Expression) lhs, re = (Expression) rhs;
			if (isTF != null) return isTF ? 
					True.from(op, le, re) : False.from(op, le, re);
			
		} catch (ReenterException e) {
			e.leave();
		} catch (NullPointerException | ClassCastException e) {}
		
		return null;
//		Expression[] expArray = lhs.toArray();
//		if (expArray == null) return null;
//		
//		final int expArraySize = expArray.length;
//		boolean equalsTrue = expArraySize > 0;
//		
//		// comparing all by adjacent pairs
//		for (int i1 = 0; i1 < expArraySize - 1; i1++) {
//			Expression e1 = expArray[i1];
//			Expression e2 = expArray[i1 + 1];
//			
//			boolean e1EqualsE2 = e1.equals(e2);
//			switch (op) {
//			
//			case Equal:	
//				equalsTrue &= e1EqualsE2; 
//				break;
//				
//			case NotEqual:	
//				equalsTrue = areAllNumbers ? equalsTrue && !e1EqualsE2 : false;
//				break;
//				
//			default: 
//				if (areAllNumbers) {
//					Number<?> num1 = (Number<?>) e1, num2 = (Number<?>) e2;
//					boolean n1IsLessThanN2 = num1.isLessThan(num2); 
//					switch (orOp) {
//					case LessThan:
//						if (n1IsLessThanN2) {equalsTrue &= n1IsLessThanN2; break;} 
//						else return FALSE;
//					case GreaterEqual:
//						if (!n1IsLessThanN2) {equalsTrue &= !n1IsLessThanN2; break;} 
//						else return FALSE;
//						
//					default: 
//						boolean n1IsLessEqualN2 = n1IsLessThanN2 && e1EqualsE2;
//						switch (orOp) {
//						case LessEqual:
//							if (n1IsLessEqualN2) {equalsTrue &= n1IsLessEqualN2; break;} 
//							else return FALSE;
//						case GreaterThan:
//							if (!n1IsLessEqualN2) {equalsTrue &= !n1IsLessEqualN2; break;} 
//							else return FALSE;
//						default:
//							break;
//						}
//					}
//				} else equalsTrue = false;
//				
//			} 
//		}
//		
//		return equalsTrue ? TRUE : this;
	}
	
	
	
	public default <T, R> R applyConst(
			Function<T, R> func, Supplier<T> inputSup) {
		return Elemental.applySkipNull(func, inputSup);
	}
	
	public static <T1, T2, R> R applySkipNull(
			BiFunction<T1, T2, R> func, Supplier<T1> input1Sup, Supplier<T2> input2Sup) {
		return Elemental.getSkipNull(()-> {
			final T1 in1 = input1Sup.get(); 
			final T2 in2 = input2Sup.get(); 
			return in1 == null || in2 == null 
					? null 
					: func.apply(in1, in2);});
	}
	
	public static <T> T getSkipNull(Supplier<T> sup) {
		return Elemental.getSkipNull(sup);
	}
	
	@SuppressWarnings("removal")
    public default Method getMethod(
			Class<?> clazz, java.lang.String name, Class<?>... parameterTypes) {
		return DebugElement.getMethod(clazz, name, parameterTypes);
	}
	
	
	
	/**
	 * @return non-null
	 */
	public default Set<? extends PathVariablePlaceholder> 
	getDirectPathVariablePlaceholders() {
		return this instanceof ConditionElement
				? ((ConditionElement) this).getDirectPathVariablePlaceholders()
				: Collections.emptySet();
	}
	
	/**
	 * @return @NotNull
	 */
	public default Set<Version<?>> getDirectVariableReferences() {
		return this instanceof ConditionElement
				? ((ConditionElement) this).getDirectVariableReferences()
				: Collections.emptySet();
	}
	
	
	
	/**
	 * @return the AST type of this expression
	 */
	public PlatformType getType();
	
	@SuppressWarnings("removal")
    public default Number<?> getOne() {
		PlatformType t = getType();
		if (t instanceof PointerType) t = ((PointerType) t).getType();
		if (t instanceof DataType) switch ((DataType) t) {
		case Int:	return Int.ONE;
		case Real:	return Real.ONE;
		default:	
		}
		return DebugElement.throwTodoException("unsupported one?");
	}
	
	/**
	 * @param ne2
	 * @return Common zero of this and {@code ae2}. 
	 * 	Or null if {@code ae2} is null or both this and {@code ae2} are in unsupported types.
	 */
	@SuppressWarnings("removal")
    public default Number<?> getOne(NumericExpression ne2) {
		if (ne2 == null) return getOne();
		
		final Number<?> ONE = getOne(), ONE2 = ne2.getOne();
		if (ONE != null) {
			final Boolean eqsOne = ONE.equals(ONE2);
			if (eqsOne != null && eqsOne) return ONE;
		}
		return DebugElement.throwTodoException("unsupported one?");
	}

	@SuppressWarnings("removal")
    public default Number<?> getZero() {
		final PlatformType t = getType();
		if (t instanceof PointerType) return Int.ZERO;
		if (t instanceof DataType) switch ((DataType) t) {
		case Int:	return Int.ZERO;
		case Real:	return Real.ZERO;
		default:	
		}
		return DebugElement.throwTodoException("unsupported zero?");
	}
	
	/**
	 * @param ne2
	 * @return Common zero of this and {@code ae2}. 
	 * 	Or null if {@code ae2} is null or both this and {@code ae2} are in unsupported types.
	 */
	@SuppressWarnings("removal")
    public default Number<?> getZero(NumericExpression ne2) {
		if (ne2 == null) return getZero();
		
		final Number<?> ZERO = getZero(), ZERO2 = ne2.getZero();
		if (ZERO != null) {
			final Boolean eqsZero = ZERO.equals(ZERO2);
			if (eqsZero != null && eqsZero) return ZERO;
		}
		return DebugElement.throwTodoException("unsupported zero?");
	}
	
	@SuppressWarnings("removal")
    public default Number<?> getPositiveInfinity() {
		final PlatformType t = getType();
		return t instanceof PlatformType 
				? ((PlatformType) t).getPositiveInfinity()
				: DebugElement.throwTodoException("non-numeric type");
	}
	
	@SuppressWarnings("removal")
    public default Number<?> getNegativeInfinity() {
		final PlatformType t = getType();
		return t instanceof PlatformType 
				? ((PlatformType) t).getNegativeInfinity()
				: DebugElement.throwTodoException("non-numeric type");
	}
	
	
	
	public default boolean isBounded() {
		return getType().isPlatformBounded();
	}
	

	
	public default Boolean isOne() {
		return getType().isNumeric()
				&& getSkipNull(()-> equals(getOne()));
	}
	
	public default Boolean isZero() {
		if (this instanceof ConditionElement) {
			final ConditionElement ce = (ConditionElement) this;
			if (ce.hasPositiveGuards() || ce.hasNegativeGuards()) return false;
		}
		return getType().isNumeric()
				&& getSkipNull(()-> equals(getZero()));
	}
	
	/**
	 * TODO: detect structural traversal?
	 * @return isPositiveInfinity() || (!isLessThan(getZero()) && !isZero())
	 */
	@SuppressWarnings("removal")
    public default Boolean isPositive() {
		try {
			if (this instanceof ConditionElement) {
				final ConditionElement ce = (ConditionElement) this;
				if (ce.hasPositiveGuards()) return true;
				if (ce.hasNegativeGuards()) return false;
			}
			return getSkipNull(()-> toNonSelfConstant().isPositive());
			
		} catch (Exception e) {
			return DebugElement.throwTodoException(e);
		}
		
//		return getZero().isLessThan((ArithmeticExpression) this);
		
//		if (initiatesStructuralTraversal()) return isPositiveByOperands();
//		
//		initiateStructuralTraversal();
//		final Boolean isLtZ = isLessThan(getZero()), isZ = isZero();
//		resetStructuralTraversal();
//		
//		try {			return isPositiveInfinity() || (!isLtZ && !isZ);
//		} catch (NullPointerException ex1) {	// isPositiveInfinity() == null (excluding false Boolean case)
//			try {		if (!isLtZ && !isZ) return true;
//			} catch (NullPointerException ex2) {	// !isLtZ && !isZ == null
//						return isPositiveByOperands();
//			}
//		}
	}
	
	/**
	 * @return isPositive() || isZero()
	 */
	@SuppressWarnings("unchecked")
	public default Boolean isPositiveOrZero() {
		return trySkipNullException(
				getMethod(NumericExpression.class, "isPositiveOrZero"),
				()-> ((ConditionElement) this).hasPositiveOrZeroGuards() ? true : null,
				()-> toNonSelfConstant().isPositiveOrZero(),
				()-> Boolean.TRUE.equals(isZero()) ? true : null,	// isZero() is faster
				()-> Boolean.TRUE.equals(isPositive()) ? true : null);
	}
	
	/**
	 * @return getPositiveInfinity() != null && !(isNegative() || isZero() || ...)
	 */
	@SuppressWarnings("unchecked")
	public default Boolean isPositiveInfinity() throws ReenterException {
		if (getPositiveInfinity() == null) return false;	// non-supporting type
		return trySkipNullException(
				getMethod(NumericExpression.class, "isPositiveInfinity"),
				()-> isBounded() ? false : null,
				()-> ((ConditionElement) this).hasPositiveGuards() ? false : null,
				()-> ((ConditionElement) this).hasNegativeGuards() ? false : null,
				()-> Boolean.TRUE.equals(isZero()) ? false : null,	// isZero() is faster
				()-> Boolean.TRUE.equals(isNegative()) ? false : null,
				()-> toNonSelfConstant().isPositiveInfinity(),
				()-> Boolean.TRUE.equals(isNegativeInfinity()) ? false : null);
	}

	/**
	 * @return isNegativeInfinity() || !isPositiveOrZero()
	 */
	@SuppressWarnings("unchecked")
	public default Boolean isNegative() 
			throws ReenterException {
		return trySkipNullException(
				getMethod(NumericExpression.class, "isNegative"),
				()-> ((ConditionElement) this).hasPositiveGuards() ? false : null,
				()-> ((ConditionElement) this).hasNegativeGuards() ? true : null,
				()-> toNonSelfConstant().isNegative(),
				()-> !isPositiveOrZero(),
				()-> Boolean.TRUE.equals(isNegativeInfinity()) ? true : null);
	}
		
	/**
	 * @return getNegativeInfinity() != null && !(isPositive() || isZero() || ...)
	 */
	@SuppressWarnings("unchecked")
	public default Boolean isNegativeInfinity() 
			throws ReenterException {
		if (getNegativeInfinity() == null) return false;	// non-supporting type
		return trySkipNullException(
				getMethod(NumericExpression.class, "isNegativeInfinity"),
				()-> isBounded() ? false : null,
				()-> ((ConditionElement) this).hasPositiveOrZeroGuards() ? false : null,
				()-> ((ConditionElement) this).hasNegativeGuards() ? false : null,
				()-> Boolean.TRUE.equals(isZero()) ? false : null,		// isZero() is faster
				()-> Boolean.TRUE.equals(isPositive()) ? false : null,
				()-> toNonSelfConstant().isNegativeInfinity(),
				// main return
				()-> Boolean.TRUE.equals(isPositiveInfinity()) ? false : null);
	}
	
	/**
	 * - < 0+, 0 < +, + < ++, etc.
	 * 
	 * @param ne2
	 * @return
	 */
	@SuppressWarnings({ "unchecked" })
	public default Boolean isLessThan(NumericExpression ne2) 
			throws ReenterException {
		if (ne2 == null) return Elemental.throwNullArgumentException("numeric expression");
		return trySkipNullException(
				getMethod(NumericExpression.class, "isLessThan", NumericExpression.class), 
				()-> toNonSelfConstant().isLessThan(ne2),
				()-> applyConst(this::isLessThan, ne2::toNonSelfConstant),
				()-> Boolean.TRUE.equals(isPositiveInfinity()) ? false : null,
				()-> Boolean.TRUE.equals(isNegativeInfinity()) ? !ne2.isNegativeInfinity() : null,
				// main but not completed returns
				()-> Boolean.TRUE.equals(isNegative()) && (ne2.isZero() || ne2.isPositive()) ? true : null, // - < 0+
				()-> isZero() && ne2.isPositive() ? true : null);                                           // 0 < +
	}

	/**
	 * @param ne2
	 * @return equals(ae2) || isLessThan(ae2)
	 */
	@SuppressWarnings({ "unchecked" })
	public default Boolean isLessEqual(NumericExpression ne2) 
			throws ReenterException {
		if (ne2 == null) return Elemental.throwNullArgumentException("numeric expression");
		return trySkipNullException(
				getMethod(NumericExpression.class, "isLessEqual", NumericExpression.class),
				()-> toNonSelfConstant().isLessEqual(ne2),
				()-> applyConst(this::isLessEqual, ne2::toNonSelfConstant),
				()-> equals(ne2) || isLessThan(ne2),	// equals(ae2) is faster, in case of !equals(ae2)
				()-> isLessThan(ne2));
	}
	
	/**
	 * @param ne2
	 * @return True if this logically equals to {@code ae2}.
	 * 	Null means objectly non-equal but logically unknown.
	 * 	Since objectly non-equal doesn't mean logically non-equal, for example, 
	 * 	tran = 314159265.0 is objectly non-equal but logically equal
	 */
	@SuppressWarnings({ "unchecked" })
	public default Boolean equals(NumericExpression ne2) 
			throws ReenterException {
		if (ne2 == null) return Elemental.throwNullArgumentException("numeric expression");
		return trySkipNullException(
				getMethod(NumericExpression.class, "equals", NumericExpression.class),
				// lhs ::= rhs -> lhs == rhs
				()-> toNonSelfConstant().equals(ne2),
				()-> applyConst(this::equals, ne2::toNonSelfConstant),
				// breaking cycle of isPositiveInfinity()
				()-> Boolean.TRUE.equals(ne2.isPositiveInfinity()) ? isPositiveInfinity() : null,
				// breaking cycle of isNegativeInfinity()
				()-> Boolean.TRUE.equals(ne2.isNegativeInfinity()) ? isNegativeInfinity() : null,
				// main return - equal-ness by 3rd party logic
				()-> equalsLogically(ne2));
	}
	
	public default Boolean equalsLogically(NumericExpression ne2) {
		return equals((Object) ne2) ? true : null;
	}
	
	
	@SuppressWarnings("unchecked")
	public default Expression negate() 
			throws ReenterException, UnsupportedOperationException {
		final NumericExpression result = trySkipNullException(
				getMethod(NumericExpression.class, "negate"),
				()-> Boolean.TRUE.equals(isZero()) ? this : null,
				()-> applyConst(con-> (NumericExpression) con.negate(), ()-> toNonSelfConstant()),
				()-> Boolean.TRUE.equals(isPositiveInfinity()) ? getNegativeInfinity() : null,
				()-> Boolean.TRUE.equals(isNegativeInfinity()) ? getPositiveInfinity() : null);
		return result instanceof Expression 
				? (Expression) result 
				: (result == null
				? null
				: SystemElement.throwUnsupportedNegation());
	}

	public default Proposition equal(NumericExpression ne2) {
		return this instanceof Expression && ne2 instanceof Expression
				? Equality.from((Expression) this, (Expression) ne2)
				: from(OrderRelation.Operator.Equal, this, ne2);
	}
	
	public default Proposition lessThan(NumericExpression ne2) {
		return this instanceof Expression && ne2 instanceof Expression
				? OrderRelation.from(
						OrderRelation.Operator.LessThan, (Expression) this, (Expression) ne2, null)
				: from(
						OrderRelation.Operator.LessThan, this, ne2);
	}
	
	public default Proposition lessEqual(NumericExpression ne2) {
		return this instanceof Expression && ne2 instanceof Expression
				? OrderRelation.from(
						OrderRelation.Operator.LessEqual, (Expression) this, (Expression) ne2, null)
				: from(
						OrderRelation.Operator.LessEqual, this, ne2);
	}
	
	
	
//	default public <R> R test(Class<Exception>[] skips, 
//			@SuppressWarnings("unchecked") Supplier<R>... testers) {
//		if (testers == null) DebugElement.throwNullArgumentException("tester");
////		if (ExceptionSkippingTesters.initiatesTesting(testers)) return null;
//		
////		ExceptionSkippingTesters.initiateTesting(testers);
//		ExceptionSkippingTesters<R> ests = new ExceptionSkippingTesters<>(this, skips);
//		for (Supplier<R> tester : Arrays.asList(testers)) ests.add(this, tester); 
//		
//		R result = ests.test();
////		ExceptionSkippingTesters.resetTesting(testers);
//		return result;
//	}
	
	@SuppressWarnings({ "unchecked", "removal" })
	public default <T> T trySkipNullException(Method callee, Supplier<T>... tries) {
		try {
			return ((SystemElement) this).trySkipNullException(
					callee, 
					JavaUtil.AST_NULL_CLASS_CAST_REENTER_EXCEPTION_CLASS, 
//					JavaUtil.AST_NULL_CLASS_CAST_UPLACEHOLDER_EXCEPTION_CLASS, 
					tries);
			
		} catch (ClassCastException e) {
			return DebugElement.throwTodoException(e);
		} catch (Exception e) {
			return Elemental.throwUnhandledException(e);
		}
	}
	
	/**
	 * Skipping intermediate null cases.
	 * 
	 * @param tries
	 * @return
	 * @throws Exception 
	 */
	@SuppressWarnings("unchecked")
	public default <T> T trySkipNullException(Supplier<T>... tries) 
			throws Exception {
		return this instanceof SystemElement
				? ((SystemElement) this).trySkipNullException(
						JavaUtil.AST_NULL_CLASS_CAST_REENTER_EXCEPTION_CLASS, 
						tries)
				: throwUnsupportedException();
	}
	
//	/**
//	 * Skipping intermediate null cases.
//	 * 
//	 * @param tries
//	 * @return
//	 * @throws Exception 
//	 */
//	@SuppressWarnings("unchecked")
//	default public <T> T trySkipNullException(TrySupplier<T, Exception>... tries) 
//			throws Exception {
//		return this instanceof SystemElement
//				? ((SystemElement) this).trySkipNullException(
//				JavaUtil.AST_NULL_CLASS_CAST_REENTER_EXCEPTION_CLASS, tries)
//				: throwUnsupportedException();
////		return trySkipNullException(
////				JavaUtil.NULL_POINTER_EXCEPTION_CLASS, tries);
////		return test(JavaUtil.NULL_POINTER_EXCEPTION_CLASS, tries);
////		return test(JavaUtil.AST_NULL_CLASS_CAST_UNCERTAIN_EXCEPTION_CLASS, tries);
//	}
	


	@SuppressWarnings("unchecked")
	public default <T> T trySkipNullClassCastException(Supplier<T>... tries) 
			throws Exception {
		return this instanceof SystemElement
				? ((SystemElement) this).trySkipNullException(
						JavaUtil.NULL_CLASS_CAST_EXCEPTION_CLASS, tries)
				: throwUnsupportedException();
//		return test(JavaUtil.NULL_CLASS_CAST_EXCEPTION_CLASS, tries);
	}
	
	@SuppressWarnings("removal")
    public default <T> T throwUnsupportedException() {
		return DebugElement.throwTodoException("unsupportred numeric expression");
	}
	
	
	
	@SuppressWarnings("removal")
    public default Expression toExpression() {
		if (this instanceof Expression) return (Expression) this;
		else return DebugElement.throwTodoException("inconvertible numeric expression");
	}
	
	public static List<? extends Expression> toExpressionList(
			List<? extends NumericExpression> neList) {
		if (neList == null) Elemental.throwNullArgumentException("numeric expression");

		final List<Expression> eargs = new ArrayList<>();
		for (NumericExpression ne : neList) eargs.add(ne.toExpression());
		return eargs;
	}
	
	
	
	@SuppressWarnings("removal")
    public default NumericExpression toConstant() {
		if (this instanceof SystemElement) {
			final Elemental elec = ((SystemElement) this).toConstant();
			// elec == this => (method)-toConstant().(method)-(method) cycle;
//			if (elec == this) DebugElement.throwTodoException("Non-reduced constant");
			if (elec == null) return null;
			if (elec instanceof NumericExpression) return (NumericExpression) elec;
			if (getType().isNumeric()) DebugElement.throwTodoException("Is this constant");
//				VOPCondGen.throwTodoException("Is this +oo?");
//				VOPCondGen.throwTodoException("Is this -oo?");
		}
		return null;
	}
	
	public default NumericExpression toNonSelfConstant() {
		final NumericExpression con = toConstant();
		return con == this ? null : con;
	}
	


	/**
	 * @return constant string of some unary numeric expressions, i.e., numbers
	 */
	@SuppressWarnings({ "unchecked" })
	public default java.lang.String toNonEmptyString() {
		try {
			return trySkipNullException(
					()-> Boolean.TRUE.equals(isZero()) ? "0" : null,
					()-> Boolean.TRUE.equals(isPositiveInfinity()) ? "+oo" : null,
					()-> Boolean.TRUE.equals(isNegativeInfinity()) ? "-oo" : null,
					()-> toNonSelfConstant().toString()
					);
			
		} catch (ReenterException e) {
			throw e;
		} catch (Exception e) {
			return Elemental.throwUnhandledException(e);
		}
	}
	
}