package fozu.ca.vodcg.condition;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Supplier;

import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.BooleanLiteral;
import org.eclipse.jdt.core.dom.CastExpression;
import org.eclipse.jdt.core.dom.CharacterLiteral;
import org.eclipse.jdt.core.dom.FieldAccess;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.InfixExpression;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.NullLiteral;
import org.eclipse.jdt.core.dom.NumberLiteral;
import org.eclipse.jdt.core.dom.ParenthesizedExpression;
import org.eclipse.jdt.core.dom.PostfixExpression;
import org.eclipse.jdt.core.dom.PrefixExpression;
import org.eclipse.jdt.core.dom.StringLiteral;
import org.eclipse.jdt.core.dom.SuperFieldAccess;
import org.eclipse.jdt.core.dom.SuperMethodInvocation;
import org.eclipse.jdt.core.dom.TypeLiteral;

import fozu.ca.DebugElement;
import fozu.ca.MultiPartitionable;
import fozu.ca.Pair;
import fozu.ca.SupplierCluster;
import fozu.ca.vodcg.ASTAddressable;
import fozu.ca.vodcg.ASTException;
import fozu.ca.vodcg.Assignable;
import fozu.ca.vodcg.SynchronousReadSet;
import fozu.ca.vodcg.SystemElement;
import fozu.ca.vodcg.UncertainException;
import fozu.ca.vodcg.UncertainPlaceholderException;
import fozu.ca.vodcg.VODCondGen;
import fozu.ca.vodcg.condition.Proposition.Operator;
import fozu.ca.vodcg.condition.data.ArithmeticGuard;
import fozu.ca.vodcg.condition.data.Char;
import fozu.ca.vodcg.condition.data.DataType;
import fozu.ca.vodcg.condition.data.Int;
import fozu.ca.vodcg.condition.data.PlatformType;
import fozu.ca.vodcg.condition.data.Pointer;
import fozu.ca.vodcg.condition.data.Real;
import fozu.ca.vodcg.condition.version.ThreadRoleMatchable;
import fozu.ca.vodcg.condition.version.Version;
import fozu.ca.vodcg.parallel.OmpDirective;
import fozu.ca.vodcg.util.ASTUtil;

/**
 * Expression	::= VariableRef | ArraySelect | FunctionCall | Arithmetic | Predicate
 * 
 * @author Kao, Chen-yi
 * 
 */
@SuppressWarnings("deprecation")
public abstract class Expression 
extends ConditionElement 
implements SideEffectElement, ThreadRoleMatchable, MultiPartitionable {

//	private static final Method METHOD_FROM_RECURSIVELY = 
//			Elemental.getMethod(Expression.class, "fromRecursively", IASTInitializerClause.class, VODCondGen.class);
	@SuppressWarnings("removal")
    private static final Method METHOD_GET_SIDE_EFFECT = 
	        DebugElement.getMethod(Expression.class, "getSideEffect");

	private static final Map<ASTNode, Expression> 
	EXPRESSION_CACHE 	= new HashMap<>();

	
	
	/**
	 * (TODO? Conditional or) Expression-al side-effect {@linkplain Proposition} store if needed.
	 * TODO? distinguish different {@link PathVariablePlaceholder}'s
	 */
//	private NavigableSet<Pair<Operator, Supplier<? extends SideEffectElement>>> sesupCache 
	private NavigableSet<Pair<Operator, SupplierCluster<? extends SideEffectElement>>> 
	sesupCache = null;
	private final Set<Supplier<Collection<OmpDirective>>> 
	ompSesupCache = new HashSet<>();
	/**
	 * The side-effect storage merges indirect sub-side-effects only once every time
	 * when {@code resetsSideEffect} is set.
	 */
//	private boolean resetsSideEffect = true;
	
	
	
	/**
	 * Constant-convenient constructor
	 * @param condGen
	 */
	protected Expression(VODCondGen condGen) {
		super(null, condGen);
	}
	
	protected Expression(final ASTAddressable rtAddr, VODCondGen condGen) {
		super(rtAddr, condGen);
	}
	


	@Override
	protected Object cloneNonConstant() {
		Expression clone = (Expression) super.cloneNonConstant();

		if (sesupCache != null) clone.sesupCache = new TreeSet<>(sesupCache);
		clone.ompSesupCache.addAll(ompSesupCache);
//		clone.asm = asm;
//		clone.assigner = null;	// reseting assigner for re-caching deeply clone-reversion-ed assigners
//		clone.isAssigned = isAssigned;
		return clone;
	}

//	@SuppressWarnings("unchecked")
//	@Override
//	public <T extends ConditionElement> T cloneReversion(
//			final Statement blockStat, final ThreadRoleMatchable role, Version<? extends PathVariable> ver) 
//					throws NoSuchVersionException {
//		final Expression cr = (Expression) super.cloneReversion(blockStat, role, ver);
//		if (cr.assigner != null) cr.assigner = cr.assigner.cloneReversion(blockStat, role, ver);
//		return (T) cr;
//	}
	
	
	
	public static void checkConsistency(Supplier<Boolean> cond, Expression e1, Expression e2) {
		if (cond == null) throwNullArgumentException("condition");
		if (tests(cond) && e1 != e2) throwTodoException("inconsistent expressions");
	}
	
	public static void checkConsistency(Supplier<Boolean> cond, Expression e1, Collection<? extends Expression> es2) {
		checkConsistency(cond, Collections.singleton(e1), es2);
	}
	
	public static void checkConsistency(Supplier<Boolean> cond, Collection<? extends Expression> es1, Collection<? extends Expression> es2) {
		if (cond == null) throwNullArgumentException("condition");
		if (es1 == null || es2 == null) throwNullArgumentException("expression");
		if (tests(cond))
			for (Expression e1 : es1)
//				if (e1 == null || e2 == null) throwNullArgumentException("expression");
				for (Expression e2 : es2) if (e1 == e2) return;
		throwTodoException("inconsistent expressions");
	}
	
	@SuppressWarnings("unchecked")
	public static void checkConsistency(Supplier<Boolean> cond, ArithmeticExpression ae1, Collection<? extends ArithmeticExpression> aes2) {
		try {
			checkConsistency(cond, (Expression) ae1, (Collection<? extends Expression>) aes2);
		} catch (ClassCastException e) {
			throwTodoException(e);
		}
	}
	
	/**
	 * @param node - either {@link IASTInitializer} or {@link IASTInitializerClause}
	 * @param e
	 */
	protected static void cache(ASTNode node, Expression e) {
//		if (e.equals(Proposition.TRUE) || e.equals(Proposition.FALSE)) Debug.throwReductionException();
		EXPRESSION_CACHE.put(node, e);
//		if (e != null) e.setScope(
//				Function.get(ASTUtil.getWritingFunctionDefinitionOf(clause), condGen));
	}
	
	/**
	 * @param node - either {@link IASTInitializer} or {@link IASTInitializerClause}
	 * @return
	 */
	protected static Expression fromCache(ASTNode node) {
//		EXPRESSION_CACHE.clear();
		return EXPRESSION_CACHE.get(node);
	}
	
	
	
	/**<pre>
	 * This method does generate side effects for assignments to take care.
	 * 
	 * A VOP asm expression is defined with limited context without 
	 * branching conditions.
	 * The branch conditions of expressions are taken care 
	 * by their side effect propositions.
	 * OV (including array name and array-selection arguments) is handled by 
	 * 
	 * Array-/PathVariable.findVersion(...).
	 *
	 * Function-call (including arguments) is handled via parsing IASTFunctionCallExpression.
	 * 
	 * Function parameters are handled as {@link IASTInitializerClause}'s.
	 * </pre>
	 * 
	 * @param exp
	 * @param condGen 
	 * @return
	 */
	public static Expression fromRecursively(
			org.eclipse.jdt.core.dom.Expression exp, final ASTAddressable rtAddr, VODCondGen condGen) 
					throws ASTException {
		if (exp == null) throwNullArgumentException("clause");
		if (condGen == null) throwNullArgumentException("scope manager");
//		if (EXPRESSION_LOCK.contains(clause)) return null;
		
		// caching results for both {@link Expression}'s and {@link Proposition}'s
//		EXPRESSION_CACHE.clear();
		Expression e = fromCache(exp);
		if (e == null) {
//		EXPRESSION_LOCK.add(clause);
			
			switch (exp.getNodeType()) {
			case ASTNode.MODULE_QUALIFIED_NAME: 
			case ASTNode.QUALIFIED_NAME: 
			case ASTNode.SIMPLE_NAME: 
				e = fromRecursively((Name) exp, rtAddr, condGen);
				break;
				
			case ASTNode.BOOLEAN_LITERAL: 
				e = Proposition.fromRecursively((BooleanLiteral) exp, rtAddr, condGen);
				break;
			case ASTNode.NUMBER_LITERAL: 
			    e = fromRecursively((NumberLiteral) exp, condGen);
			    break;
			case ASTNode.CHARACTER_LITERAL: 
			    e = fromRecursively((CharacterLiteral) exp, condGen);
			    break;
			case ASTNode.STRING_LITERAL: 
			    e = fromRecursively((StringLiteral) exp, condGen);
			    break;
			case ASTNode.TYPE_LITERAL: 
				e = fromRecursively((TypeLiteral) exp, condGen);
				break;
			case ASTNode.NULL_LITERAL: 
			    e = fromRecursively((NullLiteral) exp, condGen);
			    break;
				
			case ASTNode.PARENTHESIZED_EXPRESSION :
			    e = fromRecursively((ParenthesizedExpression) exp, rtAddr, condGen);
			    break;
			    
			case ASTNode.PREFIX_EXPRESSION: 
				e = fromRecursively((PrefixExpression) exp, rtAddr, condGen);
				break;
			case ASTNode.POSTFIX_EXPRESSION: 
			    e = fromRecursively((PostfixExpression) exp, rtAddr, condGen);
			    break;
			case ASTNode.INFIX_EXPRESSION: 
			    e = fromRecursively((InfixExpression) exp, rtAddr, condGen);
			    break;
			case ASTNode.ASSIGNMENT: 
				e = fromRecursively((org.eclipse.jdt.core.dom.Assignment) exp, rtAddr, condGen);
				break;
				
//		else if (exp instanceof IASTArraySubscriptExpression) 
//			e = ArrayPointer.fromRecursively((IASTArraySubscriptExpression) exp, rtAddr, condGen);
				
			case ASTNode.METHOD_INVOCATION: 
			case ASTNode.CONSTRUCTOR_INVOCATION: 
				e = FunctionCall.fromRecursively((MethodInvocation) exp, (Supplier<Proposition>) null, rtAddr, condGen);
				break;
			case ASTNode.SUPER_METHOD_INVOCATION: 
			case ASTNode.SUPER_CONSTRUCTOR_INVOCATION: 
				e = FunctionCall.fromRecursively((SuperMethodInvocation) exp, (Supplier<Proposition>) null, rtAddr, condGen);
				break;
				
			case ASTNode.CONDITIONAL_EXPRESSION:
				org.eclipse.jdt.core.dom.ConditionalExpression cexp = (org.eclipse.jdt.core.dom.ConditionalExpression) exp;
				e = ConditionalExpression.from(
						Proposition.fromRecursively((ASTNode) cexp.getExpression(), rtAddr, condGen), 
						fromRecursively(cexp.getThenExpression(), rtAddr, condGen),
						fromRecursively(cexp.getElseExpression(), rtAddr, condGen));
				break;
					
			case ASTNode.CAST_EXPRESSION:
				e = new CastCall((CastExpression) exp, rtAddr, condGen);
				break;
					
			case ASTNode.FIELD_ACCESS: 
				e = fromRecursively((FieldAccess) exp, rtAddr, condGen);
				break;
			case ASTNode.SUPER_FIELD_ACCESS: 
				e = fromRecursively((SuperFieldAccess) exp, rtAddr, condGen);
				break;
				
				// TODO: else if (general case for other kinds of expression)...
//		for (ASTNode child : exp.getChildren()) if (child instanceof org.eclipse.jdt.core.dom.Expression) return ...;
			}
			
			if (e == null) {
//			throwTodoException(
//					"Unsupported clause: " + ASTUtil.toStringOf(clause) 
//					+ " at " + ASTUtil.toLocationOf(clause));
				
				// for propositional expression, i.e., j++
				e = debugCallDepth((SystemElement) null, ()-> 
				Proposition.fromRecursivelyWithoutBranching(exp, null, condGen)); 
			}
			
			if (e != null) {
				cache(exp, e);
				
				// for both propositional and non-propositional expressions
//			if (sideEffect != null) e.andSideEffect(sideEffect);
				
//			if (!e.initiatesParentTraverse()) {
//				e.initiateParentTraverse();
//				e.addSideEffect(Proposition.fromParentBranchCondition(
//						clause, null, condGen));
//				e.stopParentTraverse();
//			}
			}
			
//		EXPRESSION_LOCK.remove(clause);
		}	//	end of: e == null
		
		return e;
	}
	
	
	
	private static Expression fromRecursively(
			final Name name, final ASTAddressable rtAddr, final VODCondGen condGen) 
					throws ASTException {
		// ID TODO: or other side-effect suitable's
		final Expression e = PathVariablePlaceholder.from(name.resolveBinding(), name, null, rtAddr, condGen);
		if (e != null) return e;
//		else if (!e.enters(METHOD_FROM_RECURSIVELY)) {	// letting the entering one complete the side-effect
//			e.enter(METHOD_FROM_RECURSIVELY);
//			e.andSideEffect();
//			e.leave(METHOD_FROM_RECURSIVELY);
//		}
		
		return throwTodoException("unsupported ID: " 
		        + ASTUtil.toStringOf(name) + " bound to type " + name.resolveTypeBinding());
	}
	
	
	
	/**
	 * The parsing of TypeLiteral has no side-effects.
	 * 
	 * @param idExp
	 * @param condGen
	 * @return
	 * @throws ASTException
	 */
	private static Expression fromRecursively(
			final TypeLiteral idExp, final VODCondGen condGen) 
					throws ASTException {
		assert idExp != null;
//		switch (idExp.getOperator()) {
////		case IASTTypeIdExpression.op_sizeof:
////			return VODCondGen.getCLibraryFunction("sizeof_Void");
//		default:
//		}
		return throwTodoException("unsupported Type ID expression: " 
				+ ASTUtil.toStringOf(idExp));
	}
	
	
	
	private static Expression fromRecursively(
			final FieldAccess refExp, final ASTAddressable rtAddr, final VODCondGen condGen) 
					throws ASTException {
		assert refExp != null;
		final ITypeBinding refTypeBind = refExp.resolveTypeBinding();
		
		// Non-boolean (non-binary) enum
		final Expression exp = from(refTypeBind, refExp);
		if (exp != null) return exp;
		
		// ID TODO: or other side-effect suitable's
		final Expression e = PathVariablePlaceholder.from(
				refTypeBind, refExp.getName(), null, rtAddr, condGen);
		if (e != null) return e; 
//		else if (!e.enters(METHOD_FROM_RECURSIVELY)) {	// letting the entering one complete the side-effect
//			e.enter(METHOD_FROM_RECURSIVELY);
//			e.andSideEffect();
//			e.leave(METHOD_FROM_RECURSIVELY);
//		}
		
		return throwTodoException("unsupported reference: " 
		        + ASTUtil.toStringOf(refExp) + " bound to " + refTypeBind);
	}

	
	
	/**
	 * The parsing of NumberLiteral has no side-effects.
	 * 
	 * @param lit
	 * @param condGen
	 * @return
	 */
	private static Expression fromRecursively(
			final NumberLiteral lit, final VODCondGen condGen) {
		assert lit != null;
		final String value = lit.getToken();
		final String addr = ASTUtil.toLineLocationOf(lit);

		// integer
		Expression exp = Int.from(value, addr);
		if (exp != null) return exp; 

		// float
		exp = Real.from(value, addr); 
		return exp;
	}
			
	
	
	/**
	 * The parsing of CharacterLiteral has no side-effects.
	 * 
	 * @param lit
	 * @param condGen
	 * @return
	 */
	private static Expression fromRecursively(
			final CharacterLiteral lit, final VODCondGen condGen) {
		// char
		return Char.from(lit.charValue()); 
	}
	
	
	
	/**
	 * The parsing of StringLiteral has no side-effects.
	 * 
	 * @param lit
	 * @param condGen
	 * @return
	 */
	private static Expression fromRecursively(
			final StringLiteral lit, final VODCondGen condGen) {
		// string: excluding quotation marks (bounding "'s or ''s)
		final String value = lit.getEscapedValue();
//			return fozu.ca.vodcg.condition.data.String.from(
//					ls.substring(1, ls.length() - 1).replaceAll("\\\\n", "\n"), condGen);
		return fozu.ca.vodcg.condition.data.String.from(value, condGen); 
	}
	
	
	
	/**
	 * The parsing of NullLiteral has no side-effects.
	 * 
	 * @param lit
	 * @param condGen
	 * @return
	 */
	private static Expression fromRecursively(
			final NullLiteral lit, final VODCondGen condGen) {
		// TODO: void?
		// TODO: this
		return throwTodoException("unsupported literal");
	}
	
	
	
	private static Expression fromRecursively(
			ParenthesizedExpression unary, final ASTAddressable rtAddr, VODCondGen condGen) 
					throws ASTException {
		// (exp)
		return fromRecursively(unary.getExpression(), rtAddr, condGen);
//		
//		/* *exp, original pointing level (dimension) is retrieved from 
//		 * the referenced {@link Variable} during the construction of 
//		 * {@link Version}.
//		 */
//					case IASTUnaryExpression.op_star: 
//						return Pointer.pointFromRecursively(oprd, rtAddr, condGen);
//						
//						// &exp
//					case IASTUnaryExpression.op_amper: 
//						return Pointer.depointFromRecursively(oprd, rtAddr, condGen);
	}
	
	private static Expression fromRecursively(
			PrefixExpression unary, final ASTAddressable rtAddr, VODCondGen condGen) 
					throws ASTException {
		assert unary != null;
		final org.eclipse.jdt.core.dom.PrefixExpression.Operator op = unary.getOperator();
		final org.eclipse.jdt.core.dom.Expression oprd = unary.getOperand();
		
		// Subtraction asm: --exp
		// Addition asm: ++exp
		if (op == PrefixExpression.Operator.DECREMENT || op == PrefixExpression.Operator.INCREMENT) try {
			final PathVariablePlaceholder pvd = 
			PathVariablePlaceholder.from(Assignable.from(oprd, rtAddr, condGen));
			return pvd.isDirectlyFunctional() ? pvd : Equality.from(op, pvd);
			// TODO? version-ing functional index
//			Version<FunctionalPathVariable> ver = FunctionalIntInputVersion.from(lv);
//			if (ver != null) {
//				PathVariableDelegate.from(lv).reversion(ver); 
//				return ver;
//			}
		} catch (Exception e) {
			return throwTodoException(e);
		}
			
		// unary arithmetics
		return Arithmetic.from(op, 
				fromRecursively(oprd, rtAddr, condGen));
	}

	private static Expression fromRecursively(
			PostfixExpression unary, final ASTAddressable rtAddr, VODCondGen condGen) 
					throws ASTException {
		assert unary != null;
		final org.eclipse.jdt.core.dom.PostfixExpression.Operator op = unary.getOperator();
		final org.eclipse.jdt.core.dom.Expression oprd = unary.getOperand();
		
		// Subtraction asm: exp--
		// Addition asm: exp++
		if (op == PostfixExpression.Operator.DECREMENT || op == PostfixExpression.Operator.INCREMENT) try {
			final PathVariablePlaceholder pvd = 
					PathVariablePlaceholder.from(Assignable.from(oprd, rtAddr, condGen));
			return pvd.isDirectlyFunctional() ? pvd : Equality.from(op, pvd);
			// TODO? version-ing functional index
//			Version<FunctionalPathVariable> ver = FunctionalIntInputVersion.from(lv);
//			if (ver != null) {
//				PathVariableDelegate.from(lv).reversion(ver); 
//				return ver;
//			}
		} catch (Exception e) {
			return throwTodoException(e);
		}
		
		// unary arithmetics
		return Arithmetic.from(op, 
				fromRecursively(oprd, rtAddr, condGen));
	}
	
		

	private static Expression fromRecursively(
	        Assignment binary, final ASTAddressable rtAddr, VODCondGen condGen) 
					throws ASTException {
		final Expression lhs = fromRecursively(binary.getLeftHandSide(), rtAddr, condGen), 
				rhs = fromRecursively(binary.getRightHandSide(), rtAddr, condGen);
		final Assignment.Operator binaryOp = binary.getOperator();
//		Function scope = Function.getFunctionScopeOf(binary, condGen);
		
		if (binaryOp == Assignment.Operator.ASSIGN
		        || binaryOp == Assignment.Operator.DIVIDE_ASSIGN
		        || binaryOp == Assignment.Operator.MINUS_ASSIGN
		        || binaryOp == Assignment.Operator.REMAINDER_ASSIGN
		        || binaryOp == Assignment.Operator.TIMES_ASSIGN
		        || binaryOp == Assignment.Operator.PLUS_ASSIGN
		        || binaryOp == Assignment.Operator.BIT_AND_ASSIGN
		        || binaryOp == Assignment.Operator.BIT_OR_ASSIGN
		        || binaryOp == Assignment.Operator.BIT_XOR_ASSIGN
		        || binaryOp == Assignment.Operator.LEFT_SHIFT_ASSIGN
		        || binaryOp == Assignment.Operator.RIGHT_SHIFT_SIGNED_ASSIGN
		        || binaryOp == Assignment.Operator.RIGHT_SHIFT_UNSIGNED_ASSIGN) {
			/* Assignment with equality side effect:
			 *  =, /=, -=, %=, *=, +=, TODO: &=, |=, ^=, <<=, >>=
			 */
			final Proposition eq = Equality.from(binaryOp, lhs, rhs);
//			lhs.setAssigned(eq.cacheAssignerIf());
			lhs.andSideEffect(()-> eq);
			return lhs;
		}
        return throwTodoException("unsupported binary expression");
	}

	private static Expression fromRecursively(
	        InfixExpression binary, final ASTAddressable rtAddr, VODCondGen condGen) 
                    throws ASTException {
        final Expression lhs = fromRecursively(binary.getLeftOperand(), rtAddr, condGen), 
                rhs = fromRecursively(binary.getRightOperand(), rtAddr, condGen);
        final InfixExpression.Operator binaryOp = binary.getOperator();
		// binary proposition
        if (binaryOp == InfixExpression.Operator.CONDITIONAL_AND)
			return And.from((Proposition) lhs, ()-> (Proposition) rhs);
//			return Elemental.getNonNull(()-> And.get((Proposition) lhs, ()-> (Proposition) rhs));
        if (binaryOp == InfixExpression.Operator.CONDITIONAL_OR)
			return Or.from((Proposition) lhs, ()-> (Proposition) rhs);
//			return Elemental.getNonNull(()-> Or.get((Proposition) lhs, ()-> (Proposition) rhs));

        if (binaryOp == InfixExpression.Operator.EQUALS
                || binaryOp == InfixExpression.Operator.NOT_EQUALS
                || binaryOp == InfixExpression.Operator.GREATER_EQUALS
                || binaryOp == InfixExpression.Operator.GREATER
                || binaryOp == InfixExpression.Operator.LESS_EQUALS
                || binaryOp == InfixExpression.Operator.LESS)
			// binary order relation
			return OrderRelation.fromRecursively(binaryOp, lhs, rhs);
//			return Elemental.getNonNull(()-> OrderRelation.fromRecursively(binaryOp, lhs, rhs, condGen));
		
        if (binaryOp == InfixExpression.Operator.DIVIDE
                || binaryOp == InfixExpression.Operator.MINUS
                || binaryOp == InfixExpression.Operator.REMAINDER
                || binaryOp == InfixExpression.Operator.TIMES
                || binaryOp == InfixExpression.Operator.LEFT_SHIFT
                || binaryOp == InfixExpression.Operator.PLUS
                || binaryOp == InfixExpression.Operator.AND)
			// binary arithmetics
			return Arithmetic.from(binaryOp, lhs, rhs);
//			return Elemental.getNonNull(()-> Arithmetic.from(binaryOp, lhs, rhs));
			
//        if (binaryOp == InfixExpression.Operator.OR
//                || binaryOp == InfixExpression.Operator.XOR
//                || binaryOp == InfixExpression.Operator.RIGHT_SHIFT_SIGNED
//                || binaryOp == InfixExpression.Operator.RIGHT_SHIFT_UNSIGNED)
        return throwTodoException(binaryOp + "unsupported binary expression");
	}

	
	
	private static Expression from(
			ITypeBinding typeBinding, FieldAccess addrNode) {
		assert typeBinding != null;
		if (ASTUtil.isBinary(typeBinding)) return Proposition.from(typeBinding);
		if (typeBinding.isEnum()) return Int.from(
		        (Integer) addrNode.resolveFieldBinding().getConstantValue(), 
		        ASTUtil.toLineOffsetLocationOf(addrNode));
		return null;
	}

	
	
	/**
	 * TODO: for type-checking
	 * @return non-null
	 */
	abstract public PlatformType getType();
	
	
	
//	public int getExtraSize() {
//		return toString().length() + Elemental.getAltNull(()-> getSideEffect().toString().length(), 0);
//	}
	
	/**
	 * For debugging information transmission.
	 * @return
	 */
	public IPath getFileLocation() {
		return throwTodoException("unknown location");
	}
	
//	public int getFunctionalDepth() {
//		return isConstant() || isEmpty() ? 0 : -1;
//	}
	
	@Override
	public Set<Pointer> getPointers() {
		Set<Pointer> ps = new HashSet<>();
		if (this instanceof Pointer) 
			ps.add((Pointer) this);
		else {
			final PlatformType type = getType();
			if (type == DataType.Pointer || type == DataType.Array	// excluding Void 
					|| type instanceof Pointer) 
				ps.add((Pointer) type);
		}
		return ps;
	}
	
	@Override
	final public Set<Version<?>> getVariableReferences() {
		final Set<Version<?>> vrs = new HashSet<>(super.getVariableReferences());
		vrs.addAll(getSideEffect().getDirectVariableReferences());
		return vrs;
	}
	

	
//	public Assignment getAssignment() {
//		if (tests(isAssigned()) && asm == null) 
//			throwTodoException("null asm");
//		return asm;
//	}
//	
//	/**
//	 * Not set assigned in case of that this is rhs.
//	 * @param asm
//	 */
//	private void setAssignment(Assignment asm) {
//		if (asm == null) throwNullArgumentException("asm");
//		if (tests(isConstant())) return;	// if rhs is constant
//		
//		this.asm = asm;
//	}
//	
//	public void setAssigned(Assignable asn) {
//		if (asn == null) throwNullArgumentException("assignable");
//		if (tests(asn.isAssigned())) {
//			if (asn.isCallArgument()) return;
//			setAssigned(asn.getAssigner().cloneReversion(getPrivatizingBlock(), getThreadRole(), null), 
//					asn.getFirstAssignment());
//		}
//	}
//	
//	public void setAssigned(Expression exp2) {
//		if (exp2 == null) throwNullArgumentException("expression");
//		if (tests(exp2.isAssigned())) 
//			setAssigned(exp2.getAssigner(), exp2.getAssignment());
//	}
//	
//	public void setAssigned(Version<?> ver) {
//		if (ver == null) throwNullArgumentException("version");
//		if (tests(ver.isAssigned())) debugCallDepth(()->
//		setAssigned(ver.getAssigner(), ver.getAssignment()));
//	}
//	
//	public void setAssigned(Boolean isAssigned) {this.isAssigned = isAssigned;}
//	
//	public void setAssigned(Expression lhs, Expression rhs) {
//		throwTodoException("non-equality asm");
//	}
//	
//	public void setAssigned(Expression lhs, Expression rhs, Assignment asm) {
//		setAssignment(asm);	
//		setAssigned(lhs, rhs);
//	}
//	
//	private void setAssignedInternal() {	// not override-able
////		if (assigner == null) throwNullArgumentException("assigner");
////		if (asm == null) throwNullArgumentException("asm");
//		setAssigned(true);
//	}
	
	
	
	public boolean isInAST() {
		return false;
	}
	
	/**
	 * For Z3 native array logic support.
	 * 
	 * @return
	 */
	public boolean isZ3ArrayAccess() {
		return getType().equals(DataType.Array);
	}


	
	public boolean isNumeric() {
		return getType().isNumeric();
	}
	
	abstract public boolean containsArithmetic();

	public Boolean containsNonConstArithmetic() {
		try {
			return getSkipNull(()-> 
			containsArithmetic() && !isConstant());
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}

	
	
	/**
	 * @param e2
	 * @return true if there's partial dependency (any 'variable dependency') between two expressions.
	 */
	public Boolean dependsOn(Expression e2) {
		if (e2 == this) return true;
		if (e2 instanceof VariablePlaceholder) return dependsOn((VariablePlaceholder<?>) e2);
		if (isEmpty() || tests(isConstant())) return false;	// isConstant() == null => circular dependency

		Boolean v1dov2 = null;
		if (e2 == null) throwNullArgumentException("expression");
		for (Version<?> v1 : getVariableReferences()) 
			for (Version<?> v2 : e2.getVariableReferences()) {
				v1dov2 = v1.dependsOn(v2);
				if (v1dov2 == null) continue;
				if (v1dov2) break;
			}
		return v1dov2; 
	}
	
	/**
	 * @param vp
	 * @return non-null since searching variable references is a complete operation.
	 */
	protected boolean dependsOn(VariablePlaceholder<?> vp) {
		if (vp == null) throwNullArgumentException("placeholder");
		if (tests(vp.isAssigned())) for (VariablePlaceholder<?> dvp : getDirectVariablePlaceholders()) 
			// ((VariablePlaceholder<?>) dvp).dependsOn(v) is already called at VariablePlaceholder
			if (dvp != this && tests(dvp.dependsOn(vp))) return true;
		return false;
	}
	
	public boolean dependsOn(Collection<VariablePlaceholder<?>> vars) {
		if (vars != null) for (VariablePlaceholder<?> v : vars) 
			if (tests(dependsOn(v))) return true;
		return false;
	}
	
	public boolean contains(Expression exp) {
		return this == exp;
	}
	
	
	
	/**
	 * @return true if this element generates illegally empty (path) condition 
	 * according to its current configuration.
	 */
	@Override
	public boolean isEmpty() {
//		if (Elemental.tests(isConstant())) return false;
		return (sesupCache == null || sesupCache.isEmpty())
				&& ompSesupCache.isEmpty();
	}
	
	/**
	 * @return true <em>if and only if</em> there has neither operator nor operands
	 * 	for non-constants; false if just containing constants.
	 */
	@Override
	public boolean isSemanticallyEmpty() {
		return tests(isConstant()) 
				? false	// for constant relations, s.t. Proposition.True
				: isEmpty();
	}
	


	public Expression minus() throws UnsupportedOperationException {
		return negate();
//		return debugCallDepth(()-> negate());
	}
	
	public Expression negate() throws UnsupportedOperationException {
		final Expression c = toConstant();
		return c != null 
				? c.negate() 
				: throwUnsupportedNegation();
	}

	
	
	protected void setDirty() {
//		isAssigned = null;
		super.setDirty();
	}
	
	
	
	/**
	 * Convenient guard-setting method for path condition.
	 * Almost equivalent to addSideEffect(FiniteIntegerGuard). 
	 * 
	 * @param guard
	 */
	@Override
	public void addGuard(ArithmeticGuard guard) {
		super.addGuard(guard);
		andSideEffect(()-> guard);
	}
	
	/**
	 * Convenient parallel condition appending method.
	 * 
	 * Supplier<? extends SideEffectElement> and Supplier<List<OmpDirective>> are 
	 * indistinguishable at compile time.
	 * 
	 * @param newSideEffect
	 */
	public void addOmpSideEffect(Supplier<Collection<OmpDirective>> newSideEffect) {
		if (newSideEffect == null) throwNullArgumentException("side-effect");
		
		ompSesupCache.add(newSideEffect);
	}
	


//	@Override
//	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
//		final Set<T> dvrs = new HashSet<>();
//		if (assigner != null) dvrs.addAll(assigner.getDirectVariableReferences(refType));
//		return dvrs;
//	}
	
	abstract protected void cacheDirectSideEffect();

//	public boolean hasSideEffect() {
//		return sesupCache != null && !sesupCache.isEmpty();
//	}
	
//	@Override
//	protected <T extends SideEffectElement> boolean suitsSideEffect(T newSe) {
//		return newSe instanceof Expression
//				&& Elemental.testsNot(dependsOn((Expression) newSe)) 
//				&& super.suitsSideEffect(newSe);
//	}
	
	@SuppressWarnings("unchecked")
	final public VODConditions getSideEffect() throws UncertainException {
		if (!suitsSideEffect()) return null;
		
		// handling recursive pv-placeholder-assignable getSideEffect
		if (enters(METHOD_GET_SIDE_EFFECT)) {	
			if (this instanceof PathVariablePlaceholder) 
				((PathVariablePlaceholder) this)
				.throwUncertainPlaceholderException(METHOD_GET_SIDE_EFFECT);
			else throwUncertainException(METHOD_GET_SIDE_EFFECT);
		}

		final VODCondGen cg = getCondGen();
		final VODConditions se = new VODConditions(null, cg);
		enter(METHOD_GET_SIDE_EFFECT);
		try {
			cacheDirectSideEffect();

			// assigned lhs's side-effect is added during AST parsing
			// non-assigned hence no side-effect
//			consumeSkipNull(cond-> se.clone(cond), 
//					()-> getAssigner().getSideEffect());
		} catch (UncertainPlaceholderException e) {
			e.leave();
		} catch (Exception e) {
			throwTodoException(e, METHOD_GET_SIDE_EFFECT);
		}
		
		if (sesupCache == null) 
			return log("No side-effects for " + this, METHOD_GET_SIDE_EFFECT);
		try {
		new SynchronousReadSet<>(sesupCache, "Side-effects").forEach(sep-> {
			final Operator seop = sep.getPeer1();
			final SideEffectElement see = 
					(SideEffectElement) sep.getPeer2().getKernel().get();
			if (see != null && !see.isSemanticallyEmpty()) {
				if (!suitsSideEffect(see)) 
					cg.log(null, "Such side-effect is NOT necessary: " + see);
				else if (seop == null) {
					if (se.isEmpty()) {
						if (see instanceof VODConditions) se.clone((VODConditions) see);
						else throwTodoException("unsupported cloning");
					} else if (!se.equals(see)) 
						throwTodoException("overthrowing the original side-effect");
				} else {	// including see instanceof CallProposition && see.isEmpty()
					switch (seop) {
					case And:	se.and(see);	break;
					case Or:	se.or(see);		break;
					case True:
					case False:
					case FunctionCall:
					case Iff:
					case Imply:
					case Not:
					case Xor:
					default:	throwTodoException("unsupported side-effect operation");
					}
				}
			}
		}, cg, new Class[] {UncertainException.class});
//		} catch (UncertainException e) {
//			leave(METHOD_GET_SIDE_EFFECT);
//			throw e;
		} catch (Exception e) {
			throwUnhandledException(e, METHOD_GET_SIDE_EFFECT);
		}
		if (se.hasGuards() && se.isSemanticallyEmpty()) 
			throwTodoException("empty assertion needs no guards");
		leave(METHOD_GET_SIDE_EFFECT);
//		sesupCache.clear();

//		new SynchronousReadSet<>(ompSesupCache, "OMP directive side-effects").forEach(ompSesup-> {
//			final List<OmpDirective> ompSes = ompSesup.get();
//			if (ompSes != null && !ompSes.isEmpty()) 
//				for (OmpDirective d : ompSes) {
//					ParallelCondition dc = d.toCondition();
//					if (suitsSideEffect(dc)) {
//						se.and(dc);
//						if (se.isEmpty()) throwReductionException();
//					}
//				}
//		}, cg);
//		ompSesupCache.clear();
		
		// replaced by Condition.setAssertions(...)
//		new SynchronousReadSet<>(getArithmeticGuards(), "Arithmetic Guard side-effects").forEach(g-> {
//			if (suitsSideEffect(g)) {
//				se.and(g);
//				if (se.isEmpty()) throwReductionException();
//			}
//		}, cg);
		
		if (se.getParallelCondition() != null) log("[ParaCond: " + this + "]");
		resetSideEffect(()-> se);
//		unsetSideEffect();	// even null sideEffect needs unsetting
		return se;
	}
	


	/**
	 * Convenient assertion reset method for path condition.
	 * 
	 * @param newSideEffect
	 */
	public void setSideEffect(Proposition newSideEffect) {
		if (suitsSideEffect(newSideEffect)) {
			addSideEffect(null, 
					()-> new VODConditions(null, PathCondition.from(newSideEffect), getScopeManager()));
//			resetSideEffect();
		}
	}
	
	private void resetSideEffect(Supplier<? extends SideEffectElement> newSe) {
		assert newSe != null;
		if (sesupCache == null || sesupCache.isEmpty()) addSideEffect(null, newSe);
		
		final Pair<Operator, SupplierCluster<? extends SideEffectElement>> topPair = sesupCache.first();
		assert topPair != null;
		if (topPair.getPeer1() != null) addSideEffect(null, newSe);
		else topPair.setPeer2(new SupplierCluster<>(newSe));
	}
	
	
	
	private void addSideEffect(
			Operator op, Supplier<? extends SideEffectElement> newSe) {
		assert newSe != null;
		final Pair<Operator, SupplierCluster<? extends SideEffectElement>> pair = new Pair<>(op, new SupplierCluster<>(newSe));
		if (sesupCache == null) sesupCache = new TreeSet<>(pair);
		sesupCache.add(pair);
		
		final int scsize = sesupCache.size();
		if (scsize > 1 
				&& sesupCache.higher(sesupCache.first()).getPeer1() == null)
			// sesupCache.get(1).op == sesupCache.get(2).op == null
			throwTodoException("overthrowing the original side-effect");
//			log("overthrowing the original side-effect");
		if (scsize > 100) throwTodoException("truly so many side-effects");
//		log("[se-size: " + scsize + "]" + getName());
//		log("[se-size: " + scsize + "]" + ASTUtil.toStringOf(getFileLocation()));
//		getCondGen().log(null, "[se-size: " + sesupCache.size() + "]" + toString() + ";" + toZ3SmtString(false, false));
	}
	

	
	public void addSideEffect(Function newSideEffect) {
		if (suitsSideEffect(newSideEffect)) {
			final VODConditions nse = new VODConditions(newSideEffect.getRuntimeAddress(), getCondGen());
			nse.add(newSideEffect);
			addSideEffect(Operator.And, ()-> nse);
//			resetSideEffect();
		}
	}
	
	
	
	public void andSideEffect(
			Supplier<? extends SideEffectElement> newSideEffect) {
		if (newSideEffect == null) throwNullArgumentException("side-effect");
		
		addSideEffect(Operator.And, newSideEffect);
	}

	public void andSideEffect(VODConditions newSideEffect) {
		if (suitsSideEffect(newSideEffect)) {
			addSideEffect(Operator.And, ()-> newSideEffect);
//			resetSideEffect();
		}
	}
	
	/**
	 * @param newSideEffect - may be a parallel condition from an OpenMP directive
	 */
	public void andSideEffect(ParallelCondition newSideEffect) {
		if (suitsSideEffect(newSideEffect)) {
			addSideEffect(Operator.And, 
					()-> new VODConditions(newSideEffect, null, getScopeManager()));
//			resetSideEffect();
		}
	}
	
	public void andSideEffect(PathCondition newSideEffect) {
		if (suitsSideEffect(newSideEffect)) {
			addSideEffect(Operator.And, 
					()-> new VODConditions(null, newSideEffect, getScopeManager()));
//			resetSideEffect();
		}
	}
	
	public <E extends Exception> void andSideEffectThrow(
			TrySupplier<? extends SideEffectElement, E> newSideEffect, 
			@SuppressWarnings("unchecked") Class<? extends Exception>... skips) 
					throws E {
		final List<E> nonSkips = new ArrayList<>();
		andSideEffect(newSideEffect.toSupplier(nonSkips, skips));
		if (!nonSkips.isEmpty()) throw nonSkips.get(0);
	}
	

	
	public void orSideEffect(Supplier<? extends SideEffectElement> newSideEffect) {
		if (newSideEffect == null) throwNullArgumentException("side-effect");
		
		addSideEffect(Operator.Or, newSideEffect);
	}
	
	public void orSideEffect(VODConditions newSideEffect) {
		if (suitsSideEffect(newSideEffect)) {
			addSideEffect(Operator.Or, ()-> newSideEffect);
//			resetSideEffect();
		}
	}
	
	public void implySideEffect(Supplier<VODConditions> newSideEffect) {
		if (newSideEffect == null) throwNullArgumentException("side-effect");
		
		addSideEffect(Operator.Imply, newSideEffect);
	}
	
//	protected void resetSideEffect() {
//		resetsSideEffect = true;
//		// TODO? parent.resetSideEffect();
//	}
//	
//	public boolean resetsSideEffect() {
//		return resetsSideEffect;
//	}
//	
//	private void unsetSideEffect() {
//		resetsSideEffect = false;
//		// TODO? parent.unsetSideEffect();
//	}

	
	
//	@SuppressWarnings("unchecked")
//	public <T extends ConditionElement> T substitute(Reference<?> ref1, Reference<?> ref2) {
//		final Expression ss = super.substitute(ref1, ref2);
//		if (tests(isAssigned())) ss.getAssigner().substitute(ref1, ref2);
//		return (T) ss;
//	}

	
	
	public ArithmeticExpression toArithmeticExpression() {
		return this instanceof ArithmeticExpression
				? (ArithmeticExpression) this
						: throwTodoException("unsupported expression");
	}
	
	public Proposition toProposition() {
//		if (isConstant()) return null;
		try {
			return getSkipNull(()-> getSideEffect().getAssertion().get());
			
		} catch (UncertainException e) {	// thrown by recursive getSideEffect()
			throw e;
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
//		return debugCallDepth(()-> Elemental.getSkipNull(()-> getSideEffect().getAssertions()));
	}

	
	
	public String toCanonicalString() {
		return toString().replaceAll("[\\n\\(\\)]", "");
	}

}