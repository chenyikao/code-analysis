/**
 * 
 */
package fozu.ca.vodcg.condition;

import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;

import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.InfixExpression;
import org.eclipse.jdt.core.dom.Statement;

import fozu.ca.DebugElement;
import fozu.ca.Elemental;
import fozu.ca.vodcg.ASTAddressable;
import fozu.ca.vodcg.ASTException;
import fozu.ca.vodcg.Assignable;
import fozu.ca.vodcg.ReenterException;
import fozu.ca.vodcg.SystemElement;
import fozu.ca.vodcg.UncertainException;
import fozu.ca.vodcg.VODCondGen;
import fozu.ca.vodcg.condition.Arithmetic.Operator;
import fozu.ca.vodcg.condition.data.Int;
import fozu.ca.vodcg.condition.data.Number;
import fozu.ca.vodcg.condition.data.NumericExpression;
import fozu.ca.vodcg.condition.version.FunctionallableRole;
import fozu.ca.vodcg.condition.version.ThreadRoleMatchable;
import fozu.ca.vodcg.condition.version.Version;
import fozu.ca.vodcg.util.ASTLoopUtil;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public interface ArithmeticExpression extends NumericExpression, ThreadRoleMatchable {

	public static final String NULL = "(null)";

    @SuppressWarnings("removal")
    public static ArithmeticExpression from(
			Operator op, ArithmeticExpression lhs, ArithmeticExpression rhs) 
			throws ASTException, ReenterException {
		if (op == null) Elemental.throwNullArgumentException("operator");
		if (lhs == null) Elemental.throwNullArgumentException("lhs");
		if (rhs == null) Elemental.throwNullArgumentException("rhs");

		try { switch (op) {
		case Add:                     return lhs.add(rhs);
		case Subtract:                return lhs.subtract(rhs);
		case Multiply:                return lhs.multiply(rhs);
		case ShiftLeft:               return lhs.shiftLeft(rhs);
		case BitAnd:                  return lhs.bitAnd(rhs);
		case Divide, IntegerDivide:   return lhs.divide(rhs);
		case Modulo:                  return lhs.modulo(rhs);
			
		case Max:
			// TODO: (MAX ...) MAX (MAX ...) = lhs.addAll(rhs)
			// TODO: (? ...) MAX +infinity = rhs
			// TODO: (? ...) MAX -infinity = lhs
			// TODO: (MAX ...) MAX ? = lhs.add(rhs)
		case Min:
			// TODO: (MIN ...) MIN (MIN ...) = lhs.addAll(rhs)
			// TODO: (? ...) MIN +infinity = lhs
			// TODO: (? ...) MIN -infinity = rhs
			// TODO: (MIN ...) MIN ? = lhs.add(rhs)
		default:
			DebugElement.throwTodoException(toString(op, lhs, rhs));
			break;
		} } catch (ReenterException e) {
			throw e;
		} catch (Exception e) {
			DebugElement.throwTodoException(toString(op, lhs, rhs), e);
		}
		
		return null;
	}
	

	
	/**
	 * TODO: merging with {@link Assignable#fromCanonicalIteratorOf(ForStatement)}?
	 * TODO? return Expression.from(loop.getIterationExpression()).getConstantPart()
	 * 
	 * @param loop - assumed a valid loop iteration expression
	 * @param runTimeAddr
	 * @param condGen
	 * @return an increment map of <incrementor, increment>
	 */
	@SuppressWarnings({ "unchecked", "removal" })
    public static ArithmeticExpression fromIncrementOf(ForStatement loop, final ASTAddressable runTimeAddr, VODCondGen condGen) {
		if (loop == null) DebugElement.throwNullArgumentException("loop");
		
		final List<org.eclipse.jdt.core.dom.Expression> initializers = loop.initializers();
	    return initializers.size() == 1 
	    		? ASTLoopUtil.getIncrementOf(loop, initializers.get(0), runTimeAddr, condGen)
	    		: DebugElement.throwTodoException(
	    				"unsupported multiple initializers: " + initializers);
	}
		
	
    /**<pre>
     *      incr-expr   One of the following:
     *                  ++var
     *                  var++
     *                  --var
     *                  var--
     *                  var += incr
     *                  var -= incr
     *                  var = var + incr
     *                  var = incr + var
     *                  var = var - incr
     * 
     *      var         One of the following:
     *                      A variable of a signed or unsigned integer type.
     *                      TODO: For C++, a variable of a random access iterator type.
     *                      TODO: For C, a variable of a pointer type.
     *                  If this variable would otherwise be shared, it is implicitly made private in the
     *                  loop construct. This variable must not be modified during the execution of the
     *                  for-loop other than in incr-expr. Unless the variable is specified lastprivate
     *                  or linear on the loop construct, its value after the loop is unspecified.
     * 
     *      incr        A loop invariant integer expression.
     * <br>
     * 
     * @param loop
     * @param sideEffect 
     * @param condGen 
     * @return
     */
    @SuppressWarnings("unchecked")
    public static ArithmeticExpression fromCanonicalIncrementOf(ForStatement loop, final ASTAddressable dynaAddr, VODCondGen condGen) {
        if (ASTLoopUtil.isNonCanonical(loop)) return null;
        
        final org.eclipse.jdt.core.dom.Expression init = ((List<org.eclipse.jdt.core.dom.Expression>) loop.initializers()).get(0);
        ArithmeticExpression incr = ASTLoopUtil.getIncrementOf(
                loop, init, dynaAddr, condGen);
        if (incr == null) {
            ArithmeticExpression e = ArithmeticExpression.fromIncrementOf(loop, dynaAddr, condGen);
            incr = (e instanceof Int) ? (Int) e : null; // type-checking
            
            if (incr == null) ASTLoopUtil.setNonCanonical(loop);
            else ASTLoopUtil.setIncrementOf(loop, init, incr);
        }
        return incr;
    }
    
    
	/**
	 * TODO: handling non-canonical loops.
	 * 
	 * @param loop
	 * @param wantsLowerBound
	 * @param condGen 
	 * @return
	 * @throws Exception 
	 */
	@SuppressWarnings("removal")
    static ArithmeticExpression fromBoundOf(ForStatement loop, 
			boolean wantsLowerBound, final ASTAddressable rtAddr, VODCondGen condGen) 
			throws ASTException, UncertainException {
		if (loop == null) DebugElement.throwNullArgumentException("loop");
		if (condGen == null) DebugElement.throwNullArgumentException("scope manager");
//		if (scope == null) scope = Function.getScopeOf(loop, condGen);	// lazy scope setting
		
//		LOOP_BOUND_CACHE.clear();
		ArithmeticExpression[] bounds = ASTLoopUtil.getBoundsOf(loop);
		if (bounds != null) return bounds[wantsLowerBound ? 0 : 1];
		
		final org.eclipse.jdt.core.dom.Expression ib = 
				ASTLoopUtil.getCanonicalInitialBoundOf(loop);
		final org.eclipse.jdt.core.dom.Expression tb = 
				ASTLoopUtil.getCanonicalTestBoundOf(loop, condGen);
		// TODO: suport iterator type of var/bound
		ArithmeticExpression lb = null, ub = null; 
		Expression ibe = Expression.fromRecursively(ib, rtAddr, condGen), 
				tbe = Expression.fromRecursively(tb, rtAddr, condGen); 
		final ArithmeticExpression incr = fromCanonicalIncrementOf(loop, rtAddr, condGen);
		final InfixExpression.Operator tbOp = ASTLoopUtil.getCanonicalTestOperatorToVarOf(loop, condGen);
		OrderRelation.Operator orOp;
		
		/* normalization of [ib,test-expr operator,tb] does NOT work
		 * 	-> incr <|>= 0		(doing arithmetic semantics checking of incr here)
		 *  -> ib <|<|>|>= tb	(leaving arithmetic semantics checking to Z3)
		 */
		try {
		if (tests(incr.isPositiveOrZero())) {
		    if (tbOp == InfixExpression.Operator.LESS)
		        /*
		         * tb[Or1:e0]	<	(var =	ib[Or2:e1])	&& var += |incr|
		         * (ib			=	var) >	tb			&& var += |incr|
		         * 
		         * 	=>	lb = ib[Or2:e1], 
		         * 		ub = (tb[Or1:e0] < ib[Or2:e1]) ? +oo : ib[Or2:e1]
		         */
		        orOp = OrderRelation.Operator.LessThan;
		    
		    else if (tbOp == InfixExpression.Operator.LESS_EQUALS) {
		        /*
		         * tb			<=	(var =	ib)			&& var += |incr|
		         * (ib			=	var) >=	tb			&& var += |incr|
		         * 
		         * 	=>	lb = ib[Or2:e1], 
		         * 		ub = (tb[Or1:e0] <= ib[Or2:e1]) ? +oo : ib[Or2:e1]
		         */
		        orOp = OrderRelation.Operator.LessEqual;
		        final OrderRelation.Operator orOp_ = orOp;
		        final Expression tbe_ = tbe;
		        lb = getSkipNull(()-> (ArithmeticExpression) ibe);
		        ub = getSkipNull(()-> (ArithmeticExpression) ConditionalExpression.from(
		                OrderRelation.from(orOp_, tbe_, ibe, null), Int.POSITIVE_INFINITY, ibe));
		    }
		    
		    else if (tbOp == InfixExpression.Operator.GREATER) {
		        /*
		         * (ib	=	var) <	tb	&& var += |incr|
		         * tb	>	(var =	ib)	&& var += |incr|
		         * 
		         * 	=>	lb = ib,
		         * 		ub = (ib < tb) ? tb-1 : ib
		         */
		        final Expression tbe__ = tbe;
		        lb = getSkipNull(()-> (ArithmeticExpression) ibe);
		        ub = getSkipNull(()-> (ArithmeticExpression) ConditionalExpression.from(
		                OrderRelation.from(OrderRelation.Operator.LessThan, ibe, tbe__, null), 
		                Arithmetic.from(Operator.Subtract, tbe__, Int.ONE), 
		                ibe));
		    }
		    
		    else if (tbOp == InfixExpression.Operator.GREATER_EQUALS) {
		        /* 
		         * (ib			=	var) <=	tb			&& var += |incr|
		         * tb			>=	(var =	ib)			&& var += |incr|
		         * 
		         * 	=>	lb = ib,
		         * 		ub = (ib 		 <= tb) ? tb : ib
		         */
		        final Expression tbe___ = tbe;
		        lb = getSkipNull(()-> (ArithmeticExpression) ibe);
		        ub = getSkipNull(()-> (ArithmeticExpression) ConditionalExpression.from(
		                OrderRelation.from(OrderRelation.Operator.LessEqual, ibe, tbe___, null), tbe___, ibe));
		    }
			
		} else {
		    if (tbOp == InfixExpression.Operator.LESS) {
		        /*
		         * tb			<	(var =	ib[Or2:e1])	&& var -= |incr|
		         * (ib			=	var) >	tb			&& var -= |incr|
		         * 
		         * 	=>	lb = (ib[Or2:e1] < tb[Or1:e0]) ? ib[Or2:e1] : tb[Or1:e0]+1,
		         * 		ub = ib[Or2:e1]
		         */
		        orOp = OrderRelation.Operator.LessThan;
		        if (tbe instanceof ArithmeticExpression)
		            tbe = (Expression) ((ArithmeticExpression) tbe).add(Int.ONE);
		        else DebugElement.throwTodoException(
		                tbe.toString() + " should be ArithmeticExpression!");
		        
		    } else if (tbOp == InfixExpression.Operator.LESS_EQUALS) {
		        /*
		         * tb			<=	(var =	ib)			&& var -= |incr|
		         * (ib			=	var) >=	tb			&& var -= |incr|
		         * 
		         * 	=>	lb = (ib <= tb) ? ib : tb,
		         * 		ub = ib
		         */
		        orOp = OrderRelation.Operator.LessEqual;
		        final OrderRelation.Operator orOp_ = orOp;
		        final Expression tbe_ = tbe;
		        lb = getSkipNull(()-> (ArithmeticExpression) 
		                ConditionalExpression.from(
		                        OrderRelation.from(orOp_, ibe, tbe_, null), ibe, tbe_));
		        ub = getSkipNull(()-> (ArithmeticExpression) ibe);
		    }
		    
		    else if (tbOp == InfixExpression.Operator.GREATER) {
		        /*
		         * (ib			=	var) <	tb			&& var -= |incr|
		         * tb			>	(var =	ib)			&& var -= |incr|
		         * 
		         * 	=>	lb = (ib[Or1:e0] < tb[Or2:e1]) ? -oo : ib[Or1:e0],
		         * 		ub = ib[Or1:e0]
		         */
		        orOp = OrderRelation.Operator.LessThan;
		        
		    } else if (tbOp == InfixExpression.Operator.GREATER_EQUALS) {
		        /*
		         * (ib			=	var) <=	tb			&& var -= |incr|
		         * tb			>=	(var =	ib)			&& var -= |incr|
		         * 
		         * 	=>	lb = (ib[Or1:e0] <= tb[Or2:e1]) ? -oo : ib[Or1:e0],
		         * 		ub = ib[Or1:e0]
		         */
		        orOp = OrderRelation.Operator.LessEqual;
		        final OrderRelation.Operator orOp__ = orOp;
		        final Expression tbe__ = tbe;
		        lb = getSkipNull(()-> (ArithmeticExpression) 
		                ConditionalExpression.from(
		                        OrderRelation.from(orOp__, ibe, tbe__, null), 
		                        Int.NEGATIVE_INFINITY, ibe));
		        ub = getSkipNull(()-> (ArithmeticExpression) ibe);
		    }
		}
		
		} catch (ASTException | UncertainException e) {
			throw e;
		} catch (Exception e) {
			Elemental.throwUnhandledException(e);
		}
		ASTLoopUtil.setBoundsOf(loop, bounds = new ArithmeticExpression[] {lb, ub});
		return wantsLowerBound ? lb : ub;
	}
	
	/**	<pre>
	 * 		test-expr	One of the following:
	 * 					var relational-op tb
	 * 					tb relational-op var
	 * <br>
	 * 
	 * @param loop
	 * @param condGen 
	 * @return
	 * @throws Exception 
	 */
	public static ArithmeticExpression fromLowerBoundOf(
			ForStatement loop, final ASTAddressable rtAddr, VODCondGen condGen) {
		return fromBoundOf(loop, true, rtAddr, condGen);
	}
	
	public static ArithmeticExpression fromUpperBoundOf(
			ForStatement loop, final ASTAddressable rtAddr, VODCondGen condGen) {
		return fromBoundOf(loop, false, rtAddr, condGen);
	}
	
	
	
	public static <T> T getSkipNull(Supplier<T> sup) {
		return Elemental.getSkipNull(sup);
	}

	
	
	public static boolean tests(Boolean tester) {
		return Elemental.tests(tester);
	}
	
	public default boolean containsArithmetic() {
		return true;
	}
	
	
	
	public default boolean contains(ArithmeticExpression ae2) {
		return ae2 != null && toExpression().contains(ae2.toExpression());
	}
	
	public default boolean contains(PathVariablePlaceholder pvp) {
		return pvp != null && toExpression().contains(pvp);
	}
	
	public default boolean contains(Iterable<Assignable<?>> asns) {
		if (asns != null) 
			for (Assignable<?> asn : asns)
				if (contains(asn.getPathVariablePlaceholder())) return true;

		return false;
	}
	

	
	@Override
	public default boolean derives(ThreadRoleMatchable matchable2) {
		final boolean sd = ThreadRoleMatchable.super.derives(matchable2);
		return matchable2 instanceof ArithmeticExpression
				? sd || derives(((ArithmeticExpression) matchable2).getDirectVariableReferences())
				: sd;
	}
	
	public default boolean derives(Collection<ArithmeticExpression> ae2s) {
		if (ae2s == null) Elemental.throwNullArgumentException("arithmetic expression");
		
		for (ArithmeticExpression ae2 : ae2s) 
			if (derives(ae2) || derives(ae2.getDirectVariableReferences())) return true;
		return false;
	}

	public default boolean derives(Set<Version<?>> vers) {
		return Version.derives(getDirectVariableReferences(), vers);
	}
	
	

	public default boolean isUnary() {
		return !(this instanceof Relation)
				|| ((Relation) this).isUnary();
	}
	
	@Override
	public default boolean isPrivate() {
		return ThreadRoleMatchable.super.isPrivate();
	}
	
	@SuppressWarnings({ "unchecked", "removal" })
	@Override
	public default Boolean isNegativeInfinity() 
			throws ReenterException {
		return trySkipNullException(
		        DebugElement.getMethod(ArithmeticExpression.class, "isNegativeInfinity"),
				NumericExpression.super::isNegativeInfinity,
				// main return
				()-> getZero().subtract(this).isPositiveInfinity());
	}

	
	
	@SuppressWarnings({ "unchecked" })
	public default ArithmeticExpression add(ArithmeticExpression addend) {
		if (addend == null) Elemental.throwNullArgumentException("addend");

		final Number<?> zero = getZero(addend);
		try {
			return trySkipNullException(
					// 0 + (? ...) = rhs
					()-> Boolean.TRUE.equals(isZero()) ? addend : null,
					// (? ...) + 0 = lhs
					()-> Boolean.TRUE.equals(addend.isZero()) ? this : null,
					// x + (? - x) = ?
					()-> addSubtract(addend),
					// (? - x) + x = ?
					()-> addend.addSubtract(this),
					()-> applyConst(con-> con.add(addend), ()-> (ArithmeticExpression) toNonSelfConstant()),
					()-> applyConst(this::add, ()-> (ArithmeticExpression) addend.toNonSelfConstant()),

					// oo + -oo = 0, oo + ? = oo
					()-> Boolean.TRUE.equals(isPositiveInfinity()) ? 
							(Boolean.TRUE.equals(addend.isNegativeInfinity()) ? zero : this) : null,
					// -oo + oo = 0, -oo + ? = -oo
					()-> Boolean.TRUE.equals(isNegativeInfinity()) ? 
							(Boolean.TRUE.equals(addend.isPositiveInfinity()) ? zero : this) : null,
					()-> Arithmetic.from(Operator.Add, this, addend));
			
		} catch (Exception e) {
			return Elemental.throwUnhandledException(e);
		} 
	}
	
	/**
	 * @param subtract - assumed in form s1 - s2
	 * @return aRest if this is at + aRest and at == s2.
	 */
	@SuppressWarnings("removal")
    public default ArithmeticExpression addSubtract(ArithmeticExpression subtract) {
		final Arithmetic a = (Arithmetic) this;
		final Arithmetic s = (Arithmetic) subtract;
		if (subtract == null || !s.getOp().equals(Operator.Subtract)) 
			return throwNullArithmeticException("subtraction expression");
		
		final Expression s1 = s.getOperand1();
		final Expression s2 = s.getOperand2();
		if (a.getOp().equals(Operator.Add)) {
			for (Expression at : a.getOperands()) if (at.equals(s2)) {
				final Arithmetic ass = (Arithmetic) a.rest(at);
				return ass.add(s1)
						? ass
						: DebugElement.throwTodoException("unsupported list");
			}
			return null;
		}
		
		return DebugElement.throwTodoException("unsupported augend");
	}
	

	
	@SuppressWarnings({ "unchecked" })
	public default ArithmeticExpression subtract(ArithmeticExpression subtrahend) 
			throws ReenterException {
		if (subtrahend == null) Elemental.throwNullArgumentException("subtrahend");

		final Number<?> zero = getZero(subtrahend);
		/* breaking isNegativeInfinity()-subtract(this)-subtrahend.isNegative() 
		 * and minus()/negate()-subtract(this) cycles
		 */
		try {
			return trySkipNullException(
					// (? ...) - 0 = lhs
					()-> Boolean.TRUE.equals(subtrahend.isZero()) ? this : null,
					// 0 - (- ...) = -rhs
					()-> isZero() && subtrahend.isNegative() ? 
							(ArithmeticExpression) subtrahend.negate() : null,
					// x - (? + x) = ?
					()-> subtractAdd(subtrahend),
					// (? + x) - x = ?
					()-> subtractByAugend(subtrahend),
					()-> applyConst(con-> con.subtract(subtrahend), ()-> (ArithmeticExpression) toNonSelfConstant()),
					()-> applyConst(this::subtract, ()-> (ArithmeticExpression) subtrahend.toNonSelfConstant()),

					// oo - oo = 0, oo - ? = oo
					()-> Boolean.TRUE.equals(isPositiveInfinity()) ? 
							(Boolean.TRUE.equals(subtrahend.isPositiveInfinity()) ? zero : this) : null,
					// -oo - -oo = 0, -oo - ? = -oo
					()-> Boolean.TRUE.equals(isNegativeInfinity()) ? 
							(Boolean.TRUE.equals(subtrahend.isNegativeInfinity()) ? zero : this) : null,
					// TODO: (- ...) - ? = lhs.add(rhs)
					()-> Arithmetic.from(Operator.Subtract, this, subtrahend));
			
		} catch (ReenterException e) {
			throw e;
		} catch (Exception e) {
			return Elemental.throwUnhandledException(e);
		} 
	}
	
	/**
	 * @param subtrahend
	 * @return aRest if this is at + aRest and at == subtrahend.
	 */
	@SuppressWarnings({ "unlikely-arg-type" })
	public default ArithmeticExpression subtractByAugend(ArithmeticExpression subtrahend) {
		if (subtrahend == null) Elemental.throwNullArgumentException("subtrahend");

		final Arithmetic a = (Arithmetic) this;
		if (a.getOp().equals(Operator.Add)) 
			for (Expression at : a.getOperands()) 
				if (subtrahend.equals(at)) return (ArithmeticExpression) a.rest(at);
		return null;
	}
	
	/**
	 * @param add - at + aRest
	 * @return -aRest if this is at.
	 */
	@SuppressWarnings("unlikely-arg-type")
	public default ArithmeticExpression subtractAdd(ArithmeticExpression add) {
		if (add == null) return throwNullArithmeticException("addition expression");
		
		final Arithmetic a = (Arithmetic) add;
		if (a.getOp().equals(Operator.Add)) 
			for (Expression at : a.getOperands()) 
				if (equals(at)) return (ArithmeticExpression) a.rest(at).negate();
		return null;
	}
	
	
	
	@SuppressWarnings({ "unchecked", "removal" })
	public default ArithmeticExpression multiply(ArithmeticExpression multiplicand) 
			throws UncertainException {
		if (multiplicand == null) Elemental.throwNullArgumentException("multiplicand");

		final Number<?> zero = getZero(multiplicand);
		if (zero == null) DebugElement.throwTodoException("unsupported zero type");
		final Number<?> oo = zero.getPositiveInfinity();
		final Number<?> noo = zero.getNegativeInfinity();
		try {
			return trySkipNullException(
					// 0 * A = A * 0 = 0
					()-> isZero() || multiplicand.isZero() ? zero : null,
					// 1 * A = A
					()-> Boolean.TRUE.equals(isOne()) ? multiplicand : null,
					// A * 1 = A
					()-> Boolean.TRUE.equals(multiplicand.isOne()) ? this : null,
					()-> applyConst(con-> con.multiply(multiplicand), ()-> (ArithmeticExpression) toNonSelfConstant()),
					()-> applyConst(this::multiply, ()-> (ArithmeticExpression) multiplicand.toNonSelfConstant()),

					// locally defining for breaking isNegative()-subtract(...) cycle
					// oo * (-) = -oo, oo * (+) = oo
					()-> Boolean.TRUE.equals(isPositiveInfinity()) ? 
							(Boolean.TRUE.equals(multiplicand.isNegative()) ? noo : oo) : null,
					// (-) * oo = -oo, (+) * oo = oo
					()-> Boolean.TRUE.equals(multiplicand.isPositiveInfinity()) ? 
							(Boolean.TRUE.equals(isNegative()) ? noo : oo) : null,
					// -oo * (-) = oo, -oo * (+) = -oo
					()-> Boolean.TRUE.equals(isNegativeInfinity()) ? 
							(Boolean.TRUE.equals(multiplicand.isNegative()) ? oo : noo) : null,
					// (-) * -oo = oo, (+) * -oo = -oo
					()-> Boolean.TRUE.equals(multiplicand.isNegativeInfinity()) ? 
							(Boolean.TRUE.equals(isNegative()) ? oo : noo) : null,
					()-> Arithmetic.from(Operator.Multiply, this, multiplicand));
			
		} catch (UncertainException e) {
			throw e;
		} catch (Exception e) {
			return Elemental.throwUnhandledException(e);
		} 
	}
	
	@SuppressWarnings({ "unchecked", "removal" })
	public default ArithmeticExpression bitAnd(ArithmeticExpression ae2) {
		if (ae2 == null) Elemental.throwNullArgumentException("exponent");
		
		final Number<?> zero = getZero(ae2);
		if (zero == null) DebugElement.throwTodoException("unsupported zero type");
//		final Number<?> OO = ZERO.getPositiveInfinity(), NOO = ZERO.getNegativeInfinity();
		try {
			return trySkipNullException(
					// 0 & A = 0
					()-> Boolean.TRUE.equals(isZero()) ? zero : null,
					// A & 0 = 0
					()-> Boolean.TRUE.equals(ae2.isZero()) ? zero : null,
					// 1 & A = A
					()-> Boolean.TRUE.equals(isOne()) ? ae2 : null,
					// A & 1 = A
					()-> Boolean.TRUE.equals(ae2.isOne()) ? this : null,
							
					()-> applyConst(con-> con.bitAnd(ae2), ()-> (ArithmeticExpression) toNonSelfConstant()),
					()-> applyConst(this::bitAnd, ()-> (ArithmeticExpression) ae2.toNonSelfConstant()),
					()-> Arithmetic.from(Operator.BitAnd, this, ae2));
			
//		} catch (UncertainException e) {
//			throw e;
		} catch (Exception e) {
			return Elemental.throwUnhandledException(e);
		} 
	}
	
	@SuppressWarnings({ "unchecked", "removal" })
	public default ArithmeticExpression shiftLeft(ArithmeticExpression exponent) {
		if (exponent == null) Elemental.throwNullArgumentException("exponent");
		
		final Number<?> zero = getZero(exponent);
		if (zero == null) DebugElement.throwTodoException("unsupported zero type");
//		final Number<?> OO = ZERO.getPositiveInfinity(), NOO = ZERO.getNegativeInfinity();
		try {
			return trySkipNullException(
					// 0 << A = 0
					()-> Boolean.TRUE.equals(isZero()) ? zero : null,
					// A << 0 = A
					()-> Boolean.TRUE.equals(exponent.isZero()) ? this : null,
					()-> applyConst(con-> con.shiftLeft(exponent), ()-> (ArithmeticExpression) toNonSelfConstant()),
					()-> applyConst(this::shiftLeft, ()-> (ArithmeticExpression) exponent.toNonSelfConstant()),
					
					// locally defining for breaking isNegative()-subtract(...) cycle
//					// oo * (-) = -oo, oo * (+) = oo
//					()-> isPositiveInfinity() ? (exponent.isNegative() ? NOO : OO) : null,
//					// (-) * oo = -oo, (+) * oo = oo
//					()-> exponent.isPositiveInfinity() ? (isNegative() ? NOO : OO) : null,
//					// -oo * (-) = oo, -oo * (+) = -oo
//					()-> isNegativeInfinity() ? (exponent.isNegative() ? OO : NOO) : null,
//					// (-) * -oo = oo, (+) * -oo = -oo
//					()-> exponent.isNegativeInfinity() ? (isNegative() ? OO : NOO) : null,
					()-> Arithmetic.from(Operator.ShiftLeft, this, exponent));
			
//		} catch (UncertainException e) {
//			throw e;
		} catch (Exception e) {
			return Elemental.throwUnhandledException(e);
		} 
	}
	
	@SuppressWarnings({ "unchecked", "removal" })
	public default ArithmeticExpression divide(ArithmeticExpression divisor) 
			throws UncertainException {
		if (divisor == null) Elemental.throwNullArgumentException("divisor");
		
		final Number<?> zero = getZero(divisor);
		try {
			return trySkipNullException(
					// 0 / A = 0
					()-> Boolean.TRUE.equals(isZero()) ? zero : null,
					// ? / 0 = exception
					()-> Boolean.TRUE.equals(divisor.isZero()) ? DebugElement.throwTodoException("DIVIDE by zero!") : null,
					()-> applyConst(con-> con.divide(divisor), ()-> (ArithmeticExpression) toNonSelfConstant()),
					()-> applyConst(this::divide, ()-> (ArithmeticExpression) divisor.toNonSelfConstant()),
					()-> Arithmetic.from(Operator.Divide, this, divisor));
//	TODO, type-checking:()-> Arithmetic.from(Operator.IntegerDivide, this, divisor));

		} catch (UncertainException e) {
			throw e;
		} catch (Exception e) {
			return Elemental.throwUnhandledException(e);
		} 
	}
	
	@SuppressWarnings({ "unchecked", "removal" })
	public default ArithmeticExpression modulo(ArithmeticExpression modulus) 
			throws UncertainException {
		if (modulus == null) Elemental.throwNullArgumentException("modulus");
		
		final Number<?> zero = getZero(modulus);
		try {
			return trySkipNullException(
					// 0 % A = 0
					()-> Boolean.TRUE.equals(isZero()) ? zero : null,
					// ? % 0 = exception
					()-> Boolean.TRUE.equals(modulus.isZero()) ? DebugElement.throwTodoException("MODULO by zero!") : null,
					()-> applyConst(con-> con.modulo(modulus), ()-> (ArithmeticExpression) toNonSelfConstant()),
					()-> applyConst(this::modulo, ()-> (ArithmeticExpression) modulus.toNonSelfConstant()),
					()-> Arithmetic.from(Operator.Modulo, this, modulus));

		} catch (UncertainException e) {
			throw e;
		} catch (Exception e) {
			return Elemental.throwUnhandledException(e);
		} 
	}
	
	@Override
	public default Expression negate() 
			throws ReenterException, UnsupportedOperationException {
		try {
		final Expression result = NumericExpression.super.negate();
		return result != null 
				? result 
				: Elemental.getThrow(()-> 
				(Expression) getZero().subtract(this));
		
		} catch (ReenterException e) {
			throw e;
		} catch (ClassCastException e) {
			return SystemElement.throwUnsupportedNegation();
		} catch (Exception e) {
			return Elemental.throwUnhandledException(e);
		}
	}
	
	
	
//	default public <T extends ConditionElement> T cloneIfChangeRole(
//			final ThreadRoleMatchable role) {
//		return toExpression().cloneIfChangeRole(role);
//	}
	
	public default ArithmeticExpression cloneReindex(VariablePlaceholder<?> oldIndex, VariablePlaceholder<?> newIndex) {
		return ((Expression) toExpression().clone()).substitute(oldIndex, newIndex);
	}
	
	public default <T extends ConditionElement> T cloneReversion(
			final Statement blockStat, final FunctionallableRole role, Version<? extends PathVariable> ver) {
		return toExpression().cloneReversion(blockStat, role, ver);
	}
	
	
	
	public default <T> T throwNullArithmeticException(String message) {
		if (message == null) message = "arithmetic expression";
		return Elemental.throwNullArgumentException(message);
//		TODO: throw new NullArithmeticException(); super("null Arithmetic");
	}
	
	
	
	public static String toString(
			Operator op, ArithmeticExpression lhs, ArithmeticExpression rhs) {
		return lhs == null ? NULL : lhs.toString() 
				+ " " + op == null ? NULL : op.toString() 
				+ " " + rhs == null ? NULL : rhs.toString();
	}
	
	/**
	 * @param printsVariableDeclaration
	 * @param printsFunctionDefinition
	 * @param isLhs TODO
	 * @return
	 */
	public String toZ3SmtString(
			boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs);

}