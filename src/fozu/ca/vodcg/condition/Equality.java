/**
 * 
 */
package fozu.ca.vodcg.condition;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.NavigableSet;
import java.util.Set;

import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.InfixExpression;
import org.eclipse.jdt.core.dom.PostfixExpression;
import org.eclipse.jdt.core.dom.PrefixExpression;
import org.eclipse.jdt.core.dom.VariableDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;

import fozu.ca.vodcg.ASTAddressable;
import fozu.ca.vodcg.Assignable;
import fozu.ca.vodcg.VODCondGen;
import fozu.ca.vodcg.condition.data.Int;
import fozu.ca.vodcg.condition.version.ConstArrayDeclaration;
import fozu.ca.vodcg.condition.version.FunctionalVersion;
import fozu.ca.vodcg.condition.version.VersionEnumerable;

/**
 * Equality	::= Expression ('=' Expression)+
 * 
 * @author Kao, Chen-yi
 *
 */
public class Equality extends OrderRelation 
implements AssignableExpression {

//	/**
//	 * Convenient (but hidden) constructor for a plain binary assignment, lhs = rhs.
//	 * 
//	 * @param lhs
//	 * @param rhs
//	 */
//	private Equality(Expression lhs, Expression rhs) {
//		// TODO: lhs.getScope() \/ rhs.getScope()
//		super(Operator.Equal, new HashSet<>(), lhs.getScopeManager());
//		
//		if (rhs == null) throwNullArgumentException("rhs. Empty or null operands are NOT allowed");
//		add(lhs, rhs);
//	}
	
	private static final String UNSUPPORTED_EQUALITY = "unsupported equality";



    /**
	 * @param exps - may not be empty.
	 * @param scopeManager 
	 */
	private Equality(Set<Expression> exps, VODCondGen scopeManager) {
		super(Operator.Equal, exps, scopeManager);
	}

	/**
	 * @param exps - ordered list saving assigner information
	 * 	for an assignment side-effect
	 * @param scopeManager
	 */
	private Equality(List<Expression> exps, VODCondGen scopeManager) {
		super(Operator.Equal, exps, scopeManager);
	}
	
	

	/**
	 * Convenient constructor for a plain binary assignment, lhs = rhs.
	 * 
	 * @param lhs
	 * @param rhs
	 * @param condGen 
	 */
	static public Proposition from(
			org.eclipse.jdt.core.dom.Expression lhs, org.eclipse.jdt.core.dom.Expression rhs, final ASTAddressable rtAddr, VODCondGen condGen) {
//		this(Function.getFunctionScopeOf(lhs, condGen), condGen);
		return from(Expression.fromRecursively(lhs, rtAddr, condGen), 
					Expression.fromRecursively(rhs, rtAddr, condGen));
	}
	
	static public Proposition from(
			VariableDeclaration vd, final ASTAddressable rtAddr, VODCondGen condGen) {
		if (vd == null) throwNullArgumentException("initializer");
		
//		this(Function.getFunctionScopeOf(init, condGen), condGen);
		try {
			final org.eclipse.jdt.core.dom.Expression init = vd.getInitializer();
			final Assignable<?> lhsAsn = Assignable.from(vd, rtAddr, condGen);
			if (vd instanceof VariableDeclarationFragment) {
				Proposition e = null;
				@SuppressWarnings("unchecked")
				final ConstArrayDeclaration lhs = (ConstArrayDeclaration) ConstArrayDeclaration.from((Assignable<PathVariable>) lhsAsn);
				int i = 0;
//				for (IASTInitializerClause lic : ((VariableDeclarationFragment) vd).getClauses()) {
					final Expression rhs = Expression.fromRecursively(init, rtAddr, condGen);
					final Equality eq = fromAssignment(lhs.getAssigned(i++, rhs), rhs);
					e = e == null ? eq : e.and(eq);
//				}
				return e;
				
			} else return fromAssignment(
					PathVariablePlaceholder.from(lhsAsn), Expression.fromRecursively(init, rtAddr, condGen));
		
		} catch (Exception e) {
			return throwTodoException(e);
		}
		
//		org.eclipse.jdt.core.dom.Expression asgOprd = asg.getOperand();
//		Expression operand = Expression.from(asgOprd, sideEffect);
//		if (operand instanceof PathVariable) 
//			((PathVariable) operand).reversion(LValue.from(asgOprd), scope);
	}
	
//	public static Proposition from(ArithmeticExpression lhs, ArithmeticExpression rhs) {
//		if (lhs == null) throwNullArgumentException("lhs");
//		if (rhs == null) throwNullArgumentException("rhs");
//		return from(lhs.toExpression(), rhs.toExpression());
//	}
	
	public static Proposition from(Expression lhs, Expression rhs) {
		return from(Operator.Equal, lhs, rhs, ()-> 
		new Equality(Arrays.asList(lhs, rhs), lhs.getCondGen()));
	}
	
	public static Proposition from(Collection<? extends Expression> operands) {
		Proposition eq = from(Operator.Equal, operands);
		if (eq != null && !eq.getOp().equals(Operator.Equal)) return eq;
		
		assert operands.size() > 1;
		final Iterator<? extends Expression> oit = operands.iterator();
		eq = from(oit.next(), oit.next());
		while (oit.hasNext()) eq = from(eq, oit.next());
		return eq;
	}
	
	/**
	 * Factory constructor for an AST-derived unary assignment.
	 * 
	 * @param expOp - Op code of {@link PrefixExpression}
	 * @param pvp
	 * @return
	 */
	@SuppressWarnings("deprecation")
	public static Proposition from(PrefixExpression.Operator expOp, PathVariablePlaceholder pvp) {
		if (pvp == null) throwNullArgumentException("delegate"); 
		if (pvp.isDirectlyFunctional()) {
			// Subtraction assignment: --exp
			if (expOp == PrefixExpression.Operator.DECREMENT) 
				return fromFunctional(Assignment.Operator.MINUS_ASSIGN, pvp, Int.ONE);
				
			// Addition assignment: ++exp
			if (expOp == PrefixExpression.Operator.INCREMENT) 
				return fromFunctional(Assignment.Operator.PLUS_ASSIGN, pvp, Int.ONE);
		}
		if (pvp.isLoopIterator()) return ExpressionRange.fromIteratorOf(
				pvp.getEnclosingCanonicalLoop(), pvp.cacheRuntimeAddress(), pvp.getCondGen());

		// constant counting non-functional variable versions
		final NavigableSet<PathVariablePlaceholder> prs = pvp.previousRuntimes();
		if (prs.isEmpty()) throwTodoException("not initialized placeholder");
		if (prs.size() != 1) throwTodoException("unsupported conditional placeholders");
//		Elemental.consumeNonNull(nv-> ppvd.reversion(nv), ()-> pvd.getVersion().appendConstantCounting());
		
		Proposition asm = null;
		final PathVariablePlaceholder ppvp = prs.first();
		// Subtraction assignment: --exp
		if (expOp == PrefixExpression.Operator.DECREMENT) 
			asm = fromAssignment(pvp, (Expression) ppvp.subtract(Int.ONE));

		// Addition assignment: ++exp
		else if (expOp == PrefixExpression.Operator.INCREMENT) 
			asm = fromAssignment(pvp, (Expression) ppvp.add(Int.ONE));
		
		if (asm == null) throwTodoException("unsupported assignment");
//		if (asm instanceof Equality) ((Equality) asm).setAssigned();
		return asm;
	}
	
	/**
	 * Factory constructor for an AST-derived unary assignment.
	 * 
	 * @param expOp - Op code of {@link PostfixExpression}
	 * @param pvp
	 * @return
	 */
	@SuppressWarnings("deprecation")
	public static Proposition from(PostfixExpression.Operator expOp, PathVariablePlaceholder pvp) {
		if (pvp == null) throwNullArgumentException("delegate"); 
		if (pvp.isDirectlyFunctional()) {
			// Subtraction assignment: exp--
			if (expOp == PostfixExpression.Operator.DECREMENT) 
				return fromFunctional(Assignment.Operator.MINUS_ASSIGN, pvp, Int.ONE);
			
			// Addition assignment: exp++
			if (expOp == PostfixExpression.Operator.INCREMENT) 
				return fromFunctional(Assignment.Operator.PLUS_ASSIGN, pvp, Int.ONE);
		}
		if (pvp.isLoopIterator()) return ExpressionRange.fromIteratorOf(
				pvp.getEnclosingCanonicalLoop(), pvp.cacheRuntimeAddress(), pvp.getCondGen());
		
		// constant counting non-functional variable versions
		final NavigableSet<PathVariablePlaceholder> prs = pvp.previousRuntimes();
		if (prs.isEmpty()) throwTodoException("not initialized placeholder");
		if (prs.size() != 1) throwTodoException("unsupported conditional placeholders");
//		Elemental.consumeNonNull(nv-> ppvd.reversion(nv), ()-> pvd.getVersion().appendConstantCounting());
		
		Proposition asm = null;
		final PathVariablePlaceholder ppvp = prs.first();
		// Subtraction assignment: exp--
		if (expOp == PostfixExpression.Operator.DECREMENT) 
			asm = fromAssignment(pvp, (Expression) ppvp.subtract(Int.ONE));
			
		// Addition assignment: exp++
		if (expOp == PostfixExpression.Operator.INCREMENT) 
			asm = fromAssignment(pvp, (Expression) ppvp.add(Int.ONE));
		
		if (asm == null) throwTodoException("unsupported assignment");
//		if (asm instanceof Equality) ((Equality) asm).setAssigned();
		return asm;
	}
	
	/**
	 * Factory constructor for an AST-derived binary assignment.
	 * 
	 * @param expOp - Op code of {@link IASTBinaryExpression}
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	@SuppressWarnings("deprecation")
	public static Proposition from(InfixExpression.Operator expOp, Expression lhs, final Expression rhs) {
		if (lhs == null) throwNullArgumentException("lhs");
		if (rhs == null) throwNullArgumentException("rhs");
		
		// ==: non-assignment-equality binary relational proposition
		if (expOp == InfixExpression.Operator.EQUALS) return from(lhs, rhs);
		return throwTodoException("unsupported infix-expression");
	}
		
	/**
	 * Factory constructor for an AST-derived binary assignment.
	 * 
	 * @param expOp - Op code of {@link IASTBinaryExpression}
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	public static Proposition from(Assignment.Operator expOp, Expression lhs, final Expression rhs) {
	    if (lhs == null) throwNullArgumentException("lhs");
	    if (rhs == null) throwNullArgumentException("rhs");
	    
	    // =: a ::= a makes no side-effects, even tautology
	    if (expOp == Assignment.Operator.ASSIGN && lhs != rhs) {
	        return fromAssignment(lhs, rhs);
//				eq = new Equality(Arrays.asList(lhs, rhs), ()-> rhs.getCondGen());
//				((Equality) eq).setAssigned();
	    }
	    return fromFunctional(expOp, lhs, rhs);
	}
	
	public static Proposition from(OrderRelation or) {
		if (or == null) return null;
		if (or instanceof Equality) return (Equality) or;
		if (or.getOp() == Operator.Equal) return from(or.getOperands());
		return null;
	}
	
	@SuppressWarnings("deprecation")
	private static Equality fromAssignment(Expression lhs, Expression rhs) {
		final Proposition p = from(lhs, rhs);
		if (lhs instanceof AssignableExpression) 
			((AssignableExpression) lhs).setAssigned(rhs);
		if (p instanceof Equality) {
			final Equality eq = (Equality) p;
//			eq.setAssigned();
			return eq;
		}
		return throwTodoException("unsupported assignment");
	}
	
	/**
	 * @param expOp
	 * @param lhs
	 * @param rhs
	 * @return TODO? boolean functional closure trinity:
	 * 	expanding loop iteration equality for constant/non-constant-mixed i: i1=i0+/-1, i2=i1+/-1,...
	 * 	<code><pre>
	 * 	final Proposition prop = pvd.isFunctional()
	 * 		? FunctionalIntInputVersion.from(pvd.getAssignable()).getFuncCallView().toProposition()
	 * 		: Equality.from(unaryOp, pvd);
	 */
	@SuppressWarnings({ "deprecation" })
	private static Proposition fromFunctional(Assignment.Operator expOp, Expression lhs, final Expression rhs) {
		assert lhs != null && rhs != null;
		try {
		    Expression plhs = null;
		    if (lhs instanceof AssignableExpression) {
		        final Assignable<?> lhsAsn = ((AssignableExpression) lhs).getAssignable();
		        if (lhsAsn.hasDependingLoop()) {
		            // Handling sequential loop-dependent self assignments only
		            lhs = FunctionalVersion.from(lhsAsn); 
		            plhs = ((FunctionalVersion) lhs).cloneAssigner();
		        }
		    }
		    if (plhs == null) {
		        if (lhs instanceof VersionEnumerable) 
		            plhs = (Expression) ((VersionEnumerable<?>) lhs).previousRuntimeAssigneds();
		        else if (plhs instanceof PathVariablePlaceholder) {
		            final PathVariablePlaceholder pvp = (PathVariablePlaceholder) plhs;
		            if (pvp.isLoopIterator()) return ExpressionRange.fromIteratorOf(
		                    pvp.getEnclosingCanonicalLoop(), pvp.cacheRuntimeAddress(), pvp.getCondGen());
		        }
		    }
		    if (plhs == null) throwTodoException(UNSUPPORTED_EQUALITY);
		    
		    // /=
		    if (expOp == Assignment.Operator.DIVIDE_ASSIGN)
		        // TODO: new Arithmetic(Arithmetic.Operator.IntegerDivide, ...);
		        return fromAssignment(lhs, Arithmetic.from(Arithmetic.Operator.Divide, plhs, rhs));
		    // -=
		    else if (expOp == Assignment.Operator.MINUS_ASSIGN)
		        return fromAssignment(lhs, Arithmetic.from(Arithmetic.Operator.Subtract, plhs, rhs));
		    // %=
		    else if (expOp == Assignment.Operator.REMAINDER_ASSIGN)
		        return fromAssignment(lhs, Arithmetic.from(Arithmetic.Operator.Modulo, plhs, rhs));
		    // *=
		    else if (expOp == Assignment.Operator.TIMES_ASSIGN)
		        return fromAssignment(lhs, Arithmetic.from(Arithmetic.Operator.Multiply, plhs, rhs));
		    // +=
		    else if (expOp == Assignment.Operator.PLUS_ASSIGN)
		        return fromAssignment(lhs, Arithmetic.from(Arithmetic.Operator.Add, plhs, rhs));
		    // TODO: &=?
		    else if (expOp == Assignment.Operator.BIT_AND_ASSIGN) return throwTodoException(UNSUPPORTED_EQUALITY);
		    // TODO: |=?
		    else if (expOp == Assignment.Operator.BIT_OR_ASSIGN) return throwTodoException(UNSUPPORTED_EQUALITY);
		    // TODO: ^=?
		    else if (expOp == Assignment.Operator.BIT_XOR_ASSIGN) return throwTodoException(UNSUPPORTED_EQUALITY);
		    // TODO: <<=?
		    else if (expOp == Assignment.Operator.LEFT_SHIFT_ASSIGN) return throwTodoException(UNSUPPORTED_EQUALITY);
		    // TODO: >>=?
		    else if (expOp == Assignment.Operator.RIGHT_SHIFT_SIGNED_ASSIGN) return throwTodoException(UNSUPPORTED_EQUALITY);
		    else if (expOp == Assignment.Operator.RIGHT_SHIFT_UNSIGNED_ASSIGN) return throwTodoException(UNSUPPORTED_EQUALITY);
		} catch (Exception e) {
//		}} catch (ClassCastException | NoSuchVersionException e) {
			return throwTodoException(e);
		}
		
//		if (eq instanceof Equality) ((Equality) eq).setAssigned();
		return throwTodoException(UNSUPPORTED_EQUALITY);
	}
	
	
	
	protected Proposition andByReduce(Proposition p2) {
		if (p2 == null) throwNullArgumentException("p2");
		
		Proposition result = null;
		if (p2 instanceof Equality) 
			result = andByReduce((Equality) p2);
		
		else if (p2 instanceof OrderRelation) {
			Proposition eq = Equality.from((OrderRelation) p2);
			if (eq != null) result = andByReduce(eq);
		}
		return result;
	}
	
	@SuppressWarnings("unchecked")
	private Proposition andByReduce(Equality eq2) {
		if (isEmpty()) return eq2;
		
		boolean equalsE2 = false;
		final Set<Expression> exps1 = new HashSet<>(getOperands());
		final Collection<Expression> exps2 = (Collection<Expression>) eq2.getOperands();
		for (Expression exp2 : exps2) 
			if (equalsE2 |= contains(exp2)) break;
		if (equalsE2) {
			for (Expression exp2 : exps2) 
				for (Expression exp1 : exps1) 
					if (exp1 instanceof ArithmeticExpression 
							&& exp2 instanceof ArithmeticExpression) {
						final ArithmeticExpression ae1 = (ArithmeticExpression) exp1,
								ae2 = (ArithmeticExpression) exp2;
						final Proposition equalAe2 = ae1.equal(ae2);
						if (equalAe2.isFalse()) return equalAe2;	// Contradiction!
					}
			exps1.addAll(exps2);
			return new Equality(exps1, getCondGen());
		}

		return null;
	}

//	protected Proposition andNonConst(Predicate pred) {
//		// for each exp E, if any var V of E is one of the quantifiers Q, then we have E /\ P = TODO 
//		pred.getQuantifiers();
//		if (pred instanceof Equality) {
//			List<Expression> exp2s = ((Equality) pred).getExpressions();
//			if (operands.isEmpty()) {operands.addAll(exp2s); return this;}
//			else for (Expression exp1 : operands) for (Expression exp2 : exp2s) if (exp1.equals(exp2)) {
//				operands.addAll(exp2s); return this;
//			}
//		}
//		return FALSE;
//	}

	
	
//	/**
//	 * @see fozu.caca.condition.OrderRelation#notByReduce()
//	 */
//	protected Proposition notByReduce() {
//			And eq = new And(getScopeManager());
//			Expression[] eqArray = exps.toArray(new Expression[]{});
//			for (int i = 0; i < eqArray.length - 1; i++) try {
//				eq.and(new Equality(eqArray[i], eqArray[i+1], null));
//			} catch (CoreException | InterruptedException e) {
//				e.printStackTrace();
//			}
//			return eq.not();
//	}
	
	

	@SuppressWarnings("deprecation")
	@Override
	public Expression getAssignerIf() {
		return isBinary() 
				? getRightHandSide()
				: throwTodoException(UNSUPPORTED_EQUALITY);
	}
	
//	@Override
//	public Boolean isAssigned() {
//		Boolean isA = AssignableExpression.super.isAssigned();
//		if (isA == null) {
//			isA = getAssigned() != null;
//			setAssigned(isA);
//		}
//		return isA;
//	}
	
	@SuppressWarnings("deprecation")
	@Override
	public Assignable<?> getAssignable() {
		if (isBinary()) {
			Expression lhs = getLeftHandSide();
			while (lhs != null) {
				if (lhs instanceof AssignableExpression) return ((AssignableExpression) lhs).getAssignable();
				if (lhs instanceof Relation) lhs = ((Relation) lhs).getLeftHandSide();
				else break;
			}
		}
		return throwTodoException("unsupported assignment");
	}
	
	@SuppressWarnings("deprecation")
	public Expression getAssigned() {
		if (tests(isAssigned())) {
			return isBinary() 
					? getLeftHandSide() 
					: throwTodoException("unsupported assignment");
			// inconsistent assigners since clone-reversion
//			for(Expression oprd : getOperands())
		}
		return null;
	}
	
	@SuppressWarnings("deprecation")
	@Override
	public Boolean isAssigned() {
//		if (hasAssignable()) return AssignableExpression.super.isAssigned();

		final Expression lhs = getLeftHandSide();
		if (lhs == null) return null;
		if (lhs instanceof AssignableExpression) return ((AssignableExpression) lhs).isAssigned();
		return throwTodoException("unsupported lhs");
	}

	@Override
	public void setAssigned(Boolean isAssigned) {
		Expression lhs = getLeftHandSide();
		while (true) {
			if (lhs == null) throwNullArgumentException("lhs");
			else if (lhs instanceof AssignableExpression) {
				((AssignableExpression) lhs).setAssigned(isAssigned);
				break;
			}
			else if (lhs instanceof Relation) lhs = ((Relation) lhs).getLeftHandSide();
		}
	}
	
//	@Override
//	public void setAssigned(Expression lhs, Expression rhs) {
//		setAssigned();	// for the parent assignment expression
//		if (lhs == null) throwNullArgumentException("lhs");
//		lhs.setAssigned(rhs, getAssignment());
//	}
	
	
	
	/**
	 * @see fozu.ca.vodcg.condition.OrderRelation#toConstant()
	 */
	protected Expression toConstantIf() {
//		return get(toConstantOperands());
		return this;
	}
	
	
	
	/**
	 * TODO: reusing {@link Proposition#toZ3SmtString(boolean, boolean, boolean)} to handle locals.
	 * 
	 * @fozu.caozu.ca.condition.Proposition#toZ3SmtString(boolean, boolean, boolean)
	 */
	public java.lang.String toZ3SmtString(
			boolean printsVariableDeclaration, boolean printsFunctionDefinition, boolean isLhs) {
		final Expression asd = getAssigned();
		return asd != null && asd.isZ3ArrayAccess() 
				? asd.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, true)
				: super.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, isLhs);
	}

}