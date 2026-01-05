package fozu.ca.vodcg.util;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.TreeSet;

import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.ExpressionStatement;
import org.eclipse.jdt.core.dom.IASTDeclaration;
import org.eclipse.jdt.core.dom.IASTDeclarationStatement;
import org.eclipse.jdt.core.dom.IASTDeclarator;
import org.eclipse.jdt.core.dom.IASTEqualsInitializer;
import org.eclipse.jdt.core.dom.IASTExpressionStatement;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.IASTFunctionDefinition;
import org.eclipse.jdt.core.dom.IASTInitializer;
import org.eclipse.jdt.core.dom.IASTInitializerClause;
import org.eclipse.jdt.core.dom.IASTLiteralExpression;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.PostfixExpression;
import org.eclipse.jdt.core.dom.PrefixExpression;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.IASTSimpleDeclaration;
import org.eclipse.jdt.core.dom.Statement;
import org.eclipse.jdt.core.dom.VariableDeclarationExpression;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.core.dom.IASTUnaryExpression;
import org.eclipse.jdt.core.dom.InfixExpression;
import org.eclipse.jdt.core.dom.MethodDeclaration;

import fozu.ca.DebugElement;
import fozu.ca.Elemental;
import fozu.ca.vodcg.ASTAddressable;
import fozu.ca.vodcg.SystemElement;
import fozu.ca.vodcg.VODCondGen;
import fozu.ca.vodcg.condition.ArithmeticExpression;
import fozu.ca.vodcg.condition.Expression;
import fozu.ca.vodcg.condition.ExpressionRange;
import fozu.ca.vodcg.condition.data.Int;
import fozu.ca.vodcg.parallel.OmpDirective;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public final class ASTLoopUtil {

	public enum Fragment {initializers, expression, updaters};
	
	static final Set<ForStatement> NON_CANONICAL_LOOP_CACHE = new HashSet<>();

	//	private static final Map<ForStatement, IASTDeclarator>	LOOP_INITIAL_DECL_CACHE 		= new HashMap<>();

	private static final Map<ForStatement, Expression> 
	LOOP_INITIAL_BOUND_CACHE 	= new HashMap<>();
	private static final Map<ForStatement, Expression> 	
	LOOP_TEST_BOUND_CACHE 		= new HashMap<>();
	private static final Map<ForStatement, Integer> 		
	LOOP_TEST_OP_TO_VAR_CACHE 	= new HashMap<>();

	private static final Map<ForStatement, ArithmeticExpression[]> 	
	LOOP_BOUND_CACHE 		= new HashMap<>();
	private static final Map<ForStatement, Map<org.eclipse.jdt.core.dom.Expression, ArithmeticExpression>> 			
	LOOP_INCREMENT_CACHE	= new HashMap<>();
	
	// TODO: caching all reusable utility method results
	
	private ASTLoopUtil() {}

	
	
	public static boolean isConstant(ForStatement loop, final ASTAddressable runTimeAddr, VODCondGen condGen) {
		if (loop == null) return false;
		if (isInitializedConstantly(loop) && isConditionedConstantly(loop) && iteratesConstantly(loop)) return true;
		return Elemental.tests(ExpressionRange.fromIteratorOf(loop, runTimeAddr, condGen).isConstant());
	}
	


	@SuppressWarnings("removal")
    public static ArithmeticExpression[] getBoundsOf(Statement loop) {
		if (loop instanceof ForStatement) return getBoundsOf((ForStatement) loop);
		return DebugElement.throwTodoException("unsupported loop");
	}
	
	public static ArithmeticExpression[] getBoundsOf(ForStatement loop) {
		return LOOP_BOUND_CACHE.get(loop);
	}

	public static ArithmeticExpression getLowerBoundOf(Statement loop) {
		return getBoundsOf(loop)[0];
	}
	
	public static ArithmeticExpression getUpperBoundOf(Statement loop) {
		return getBoundsOf(loop)[1];
	}
	
	
	
	/**
	 * 
	 * @param loop
	 * @return
	 */
	public static Expression getSingleIteratorOf(ForStatement loop, Fragment location) {
	    org.eclipse.jdt.core.dom.Expression lie = loop.getExpression();
		if (lie instanceof IASTUnaryExpression) lie = ((IASTUnaryExpression) lie).getOperand();
		
		// binary incr-expr
		else if (lie instanceof Assignment) {
		    final Assignment bie = (Assignment) lie;
			final Assignment.Operator op = bie.getOperator();
			if (op == Assignment.Operator.PLUS_ASSIGN            // var += incr
			        || op == Assignment.Operator.MINUS_ASSIGN    // var -= incr
			        || op == Assignment.Operator.ASSIGN) 
				// 					var = var + incr
				//					var = incr + var
				// 					var = var - incr
			    lie = bie.getLeftHandSide(); 
			// else TODO
		}
		return lie;
	}
	
	/**
	 * 
	 * @param loop
	 * @return
	 */
	public static Name getCanonicalIteratorOf(ForStatement loop) {
		if (isNonCanonical(loop)) return null;
		
		final Name isi = ASTUtil.getNameOf(getSingleIteratorOf(loop, Fragment.initializers));
		return ASTUtil.equals(isi, ASTUtil.getNameOf(getSingleIteratorOf(loop, Fragment.expression)), true)
				&& ASTUtil.equals(isi, ASTUtil.getNameOf(getSingleIteratorOf(loop, Fragment.updaters)), true)
				? isi : null; 
	}
	
	@SuppressWarnings("removal")
    public static IASTInitializerClause getCanonicalInitialBoundOf(ForStatement loop) {
		if (isNonCanonical(loop)) return null;
		
		IASTInitializerClause ib = LOOP_INITIAL_BOUND_CACHE.get(loop);
		if (ib != null) return ib;
		
		ib = getCanonicalInitializersOf(loop);
//		if (ASTLValueComputer.isUnaryAssignment(ib)) Debug.throwTodoException("unsupported bound?");
		if (ASTAssignableComputer.isBinaryAssignment(ib)) ib = ((Assignment) ib).getOperand2();
		else DebugElement.throwTodoException("unsupported bound");

		if (ib != null) LOOP_INITIAL_BOUND_CACHE.put(loop, ib);
		return ib;
	}
	
	/**<pre>
	 *	for (init-expr; test-expr; incr-expr) structured-block
	 * 		init-expr 	One of the following:
	 * 					var = lb
	 * 					integer-type var = lb
	 * 					random-access-iterator-type var = lb
	 * 					pointer-type var = lb
	 * 
	 *		var 		One of the following:
	 *						A variable of a signed or unsigned integer type.
	 *						TODO: For C++, a variable of a random access iterator type.
	 *						TODO: For C, a variable of a pointer type.
	 *					If this variable would otherwise be shared, it is implicitly made private in the
	 *					loop construct. This variable must not be modified during the execution of the
	 *					for-loop other than in incr-expr. Unless the variable is specified lastprivate
	 *					or linear on the loop construct, its value after the loop is unspecified.
	 * 
	 *		lb and b 	Loop invariant expressions of a type compatible with the type of var.
	 * <br>
	 * 
	 * @param loop
	 * @return
	 */
    @SuppressWarnings({ "removal", "unchecked" })
    public static VariableDeclarationExpression getCanonicalInitializersOf(ForStatement loop) {
        if (isNonCanonical(loop)) return null;
//				TODO: IASTDeclarator idr = LOOP_INITIAL_DECL_CACHE.get(loop);
//				if (idr == null) {
//					LOOP_INITIAL_DECL_CACHE.put(declStat, idr = ((IASTSimpleDeclaration) idn).getDeclarators()[0]);
//				}
        
		for (final org.eclipse.jdt.core.dom.Expression iz : (List<org.eclipse.jdt.core.dom.Expression>) loop.initializers()) {
		    if (iz instanceof VariableDeclarationExpression) {
		        return (VariableDeclarationExpression) iz;
		        
		    } else {
		        /*
		         * The list should consist of either a list of so called statement expressions (JLS2, 14.8), 
		         * or a single VariableDeclarationExpression. Otherwise, the for statement would have no Java source equivalent.
		         */
		        setNonCanonical(loop);
		        return DebugElement.throwTodoException("list of so called statement expressions (JLS2, 14.8)");
		    }
		}
		
        return null;
	}

	/**	<pre>
	 * 		test-expr	One of the following:
	 * 					var relational-op b
	 * 					b relational-op var
	 * 
	 *		var 		One of the following:
	 *						A variable of a signed or unsigned integer type.
	 *						TODO: For C++, a variable of a random access iterator type.
	 *						TODO: For C, a variable of a pointer type.
	 *					If this variable would otherwise be shared, it is implicitly made private in the
	 *					loop construct. This variable must not be modified during the execution of the
	 *					for-loop other than in incr-expr. Unless the variable is specified lastprivate
	 *					or linear on the loop construct, its value after the loop is unspecified.
	 *
	 *		relational-op 	One of the following:
	 * 						<
	 * 						<=
	 * 						>
	 * 						>=
	 * 
	 *		lb and b 	Loop invariant expressions of a type compatible with the type of var.
	 * <br>
	 * 
	 * @param loop
	 * @param condGen 
	 * @return
	 */
	public static Expression getCanonicalTestBoundOf(
			ForStatement loop, VODCondGen condGen) {
		return (Expression) getCanonicalTestOpToVarOrBoundOf(loop, true, condGen);
	}
	
	@SuppressWarnings("removal")
    public static int getCanonicalTestOperatorToVarOf(
			ForStatement loop, VODCondGen condGen) {
		Object op = getCanonicalTestOpToVarOrBoundOf(loop, false, condGen);
		if (op instanceof Integer) return (int) op;
		DebugElement.throwTodoException("Non-canonical loop?");
		return -1;
	}
	
	private static Object getCanonicalTestOpToVarOrBoundOf(
			ForStatement loop, boolean wantsBound, VODCondGen condGen) {
		if (isNonCanonical(loop)) return null;

		Expression tb = LOOP_TEST_BOUND_CACHE.get(loop);
		Integer top = LOOP_TEST_OP_TO_VAR_CACHE.get(loop);
		if (tb == null || top == null) {
			final org.eclipse.jdt.core.dom.Expression condExp = loop.getConditionExpression();
			if (condExp instanceof Assignment) {
				final Assignment condBin = (Assignment) condExp;
				final int op = condBin.getOperator();
				final Expression oprd1 = condBin.getOperand1(), oprd2 = condBin.getOperand2(), 
						it = getCanonicalIteratorOf(loop);
				if (ASTAssignableComputer.getDependentOnBy(oprd1, it) != null) {	// var relational-op b
					tb = oprd2; switch (op) {
					case Assignment.op_lessThan: top = Assignment.op_greaterThan; break;
					case Assignment.op_lessEqual: top = Assignment.op_greaterEqual; break;
					case Assignment.op_greaterThan: top = Assignment.op_lessThan; break;
					case Assignment.op_greaterEqual: top = Assignment.op_lessEqual; break;
					}
				}
				else if (ASTAssignableComputer.getDependentOnBy(oprd2, it) != null) {	// b relational-op var
					tb = oprd1; top = op;
				}
				// tb keeps null if loop is not canonical 
			}

			if (tb == null || top == null) setNonCanonical(loop);
			else {
				LOOP_TEST_BOUND_CACHE.put(loop, tb);
				LOOP_TEST_OP_TO_VAR_CACHE.put(loop, top);
			}
		}
		return wantsBound ? tb : top;
	}

	/**<pre>
	 * ({@linkplain OpenMP 嚜瞥ttp://www.openmp.org/mp-documents/openmp-4.5.pdf})
	 * 
	 * 嚜�2.6 Canonical Loop Form
	 * 	A loop has canonical loop form if it conforms to the following:
	 * 
	 * 		for (init-expr; test-expr; incr-expr) structured-block
	 * 			init-expr 	One of the following:
	 * 						var = lb
	 * 						integer-type var = lb
	 * 						random-access-iterator-type var = lb
	 * 						pointer-type var = lb
	 * 
	 * 			test-expr 	One of the following:
	 * 						var relational-op b
	 * 						b relational-op var
	 * 
	 * 			incr-expr 	One of the following:
	 * 						++var
	 * 						var++
	 * 						--var
	 * 						var--
	 * 						var += incr
	 * 						var -= incr
	 * 						var = var + incr
	 * 						var = incr + var
	 * 						var = var - incr
	 * 
	 * 			var 		One of the following:
	 * 							A variable of a signed or unsigned integer type.
	 * 							TODO: For C++, a variable of a random access iterator type.
	 * 							TODO: For C, a variable of a pointer type.
	 * 						If this variable would otherwise be shared, it is implicitly made private in the
	 * 						loop construct. This variable must not be modified during the execution of the
	 * 						for-loop other than in incr-expr. Unless the variable is specified lastprivate
	 * 						or linear on the loop construct, its value after the loop is unspecified.
	 * 
	 * 			relational-op 	One of the following:
	 * 							<
	 * 							<=
	 * 							>
	 * 							>=
	 * 
	 * 			lb and b 	Loop invariant expressions of a type compatible with the type of var.
	 * 
	 * 			incr 		A loop invariant integer expression.
	 * 
	 * 	The canonical form allows the iteration count of all associated loops to be computed before
	 * 	executing the outermost loop. The computation is performed for each loop in an integer type. This
	 * 	type is derived from the type of var as follows:
	 * 
	 * 		�� 	If var is of an integer type, then the type is the type of var.
	 * 		�� 	TODO: For C++, if var is of a random access iterator type, then the type is the type that would 
	 * 			be used by std::distance applied to variables of the type of var.
	 * 		�� 	TODO: For C, if var is of a pointer type, then the type is ptrdiff_t.
	 * 
	 * 	The behavior is unspecified if any intermediate result required to compute the iteration count
	 * 	cannot be represented in the type determined above.
	 * 
	 * 	There is no implied synchronization during the evaluation of the lb, b, or incr expressions. It is
	 *  unspecified whether, in what order, or how many times any side effects within the lb, b, or incr
	 *	expressions occur.
	 *
	 *	Note �� Random access iterators are required to support random access to elements in constant
	 *	time. Other iterators are precluded by the restrictions since they can take linear time or offer limited
	 *	functionality. It is therefore advisable to use tasks to parallelize those cases.
	 *
	 *	Restrictions
	 *	
	 *	The following restrictions also apply:
	 *	
	 *		�� 	If test-expr is of the form var relational-op b and relational-op is < or <= then incr-expr must
	 *			cause var to increase on each iteration of the loop. If test-expr is of the form 
	 *			'var relational-op b' and relational-op is > or >= then incr-expr must cause var to decrease on 
	 *			each iteration of the loop.
	 *		�� 	If test-expr is of the form 'b relational-op var' and relational-op is < or <= then incr-expr must
	 *			cause var to decrease on each iteration of the loop. If test-expr is of the form 
	 *			'b relational-op var' and relational-op is > or >= then incr-expr must cause var to increase on 
	 *			each iteration of the loop.
	 *		�� 	TODO: For C++, in the simd construct the only random access iterator types that are allowed for 
	 *			var are pointer types.
	 *		�� 	The b, lb and incr expressions may not reference var of any of the associated loops.
	 * <br>
	 *
	 * @param loop
	 * @param sideEffect 
	 * @param condGen 
	 * @return
	 */
	public static boolean isCanonical(ForStatement loop, VODCondGen condGen) {
		if (isNonCanonical(loop)) return false;
		if (getCanonicalInitialBoundOf(loop) == null 
				|| getCanonicalTestBoundOf(loop, condGen) == null)
//				|| Int.fromCanonicalIncrementOf(loop, condGen) == null) 
			return false;
		return true;
	}
	
	/**
	 * @param loop
	 * @return
	 */
	public static boolean isNonCanonical(ForStatement loop) {
		return loop == null || NON_CANONICAL_LOOP_CACHE.contains(loop);
	}
	
	/**
	 * @param loop
	 */
	public static void setNonCanonical(ForStatement loop) {
		NON_CANONICAL_LOOP_CACHE.add(loop);
	}
	
	public static ArithmeticExpression[] setBoundsOf(ForStatement loop, ArithmeticExpression[] bounds) {
		return LOOP_BOUND_CACHE.put(loop, bounds);
	}
	


	/**<pre>
	 * Retrieving the direct parent loop within the same function definition.
	 * </pre>
	 * 
	 * @param node
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public static ForStatement getEnclosingLoopOf(ASTNode node) {
		return (ForStatement) ASTUtil.getAncestorOfAsUnless(
				node, 
				new Class[] {ForStatement.class},
				new Class[] {MethodDeclaration.class}, 
				false);
	}
	
	/**<pre>
	 * Retrieving the direct parent loop within the same function definition.
	 * 
	 * Only supporting the OpenMP canonical for-loop 
	 * ({@linkplain OpenMP http://www.openmp.org/mp-documents/openmp-4.5.pdf}).
	 * 
	 * TODO: getEnclosingLoopCondition(...) for handling break/continue statements and while-loop conditions.
	 * <br>
	 * 
	 * @param innerLoop
	 * @return
	 */
	public static ForStatement getEnclosingLoopOf(ForStatement innerLoop) {
		return (ForStatement) ASTUtil.getAncestorOfAsUnless(
				innerLoop, 
				ASTUtil.AST_FOR_TYPE,
				ASTUtil.AST_FUNCTION_DEFINITION, 
				false);
	}
	
	
	
	public static boolean isLoop(Statement stat) {
		for (Class<Statement> clz : ASTUtil.AST_LOOP_TYPES) 
			if (clz.isInstance(stat)) return true;
		return false;
	}
	
	public static boolean isLoopParallel(Statement loop, VODCondGen condGen) {
		if (!isLoop(loop)) return false;
		
		return Elemental.tests(()-> 
		OmpDirective.fromEnclosing(loop, condGen).getStatement() == loop);
	}
	
	/**<pre>
	 * Constant iteration is stronger than the loop invariant iteration.
	 * 
	 *		lb and b 	Loop invariant expressions of a type compatible with the type of var.
	 *		incr 		A loop invariant integer expression.
	 * <br>
	 *
	 * @param i - the loop iterator
	 * @return
	 */
	public static boolean isLoopIteratorConstant(Name i) {
		final org.eclipse.jdt.core.dom.Expression exp = (org.eclipse.jdt.core.dom.Expression) i.getParent().getParent();	//bypassing IASTIdExpression
		ForStatement loop;

		/*	for (init-expr; test-expr; incr-expr) structured-block
		 * 		init-expr 	One of the following:
		 * 					var = lb
		 * 					TODO: integer-type var = lb
		 * 					TODO: random-access-iterator-type var = lb
		 * 					TODO: pointer-type var = lb
		 */ 
		if (ASTAssignableComputer.isPlainBinaryAssignment(exp)) {	// when exp is the assignment part of init-expr
			//bypassing the IASTExpressionStatement initializer statement
			loop = (ForStatement) exp.getParent().getParent();	
			return ASTAssignableComputer.isConstantAssignment((Assignment) exp) 
					&& isConditionedConstantly(loop) && iteratesConstantly(loop);
		}

		/* 		test-expr 	One of the following:
		 * 					var relational-op b
		 * 					b relational-op var
		 */
		if (ASTUtil.isBinaryRelation(exp)) {	// exp is test-expr
			loop = (ForStatement) exp.getParent();
			return isInitializedConstantly(loop) 
					&& isRelatedConstantly((Assignment) exp) && iteratesConstantly(loop);
		}

		/* 		incr-expr 	One of the following:
		 * 					++var
		 * 					var++
		 * 					--var
		 * 					var--
		 * 					var += incr
		 * 					var -= incr
		 * 					var = var + incr
		 *					var = incr + var
		 * 					var = var - incr
		 * 
		 *		var 		One of the following:
		 *						A variable of a signed or unsigned integer type.
		 *						TODO: For C++, a variable of a random access iterator type.
		 *						TODO: For C, a variable of a pointer type.
		 *					If this variable would otherwise be shared, it is implicitly made private in the
		 *					loop construct. This variable must not be modified during the execution of the
		 *					for-loop other than in incr-expr. Unless the variable is specified lastprivate
		 *					or linear on the loop construct, its value after the loop is unspecified.
		 */ 
		if (ASTAssignableComputer.isRewritingAssignment(exp)) {	// exp is incr-expr, which only concerns linear increments
			loop = (ForStatement) exp.getParent();
			return isInitializedConstantly(loop) 
					&& isConditionedConstantly(loop) 
					&& (exp instanceof Assignment)?increasesConstantly((Assignment) exp):true;
		}
		
		return false;
	}



	@SuppressWarnings("unchecked")
	public static boolean isInitializedConstantly(ForStatement loop) {
		if (loop == null) SystemElement.throwNullArgumentException("loop");
		
		//	for (init-expr; test-expr; incr-expr) structured-block
		for (org.eclipse.jdt.core.dom.Expression init : (List<org.eclipse.jdt.core.dom.Expression>) loop.initializers()) {
			/* 		init-expr 	One of the following:
			 * 					var = lb
			 */
			if (init instanceof VariableDeclarationExpression) {
				for (VariableDeclarationFragment initFrag : (List<VariableDeclarationFragment>) ((VariableDeclarationExpression) init).fragments()) {
					final org.eclipse.jdt.core.dom.Expression initExp = ((VariableDeclarationFragment) initFrag).getInitializer();
					if (ASTAssignableComputer.isPlainBinaryAssignment(initExp))
						return ASTAssignableComputer.isConstantAssignment((Assignment) initExp);
				}
			} else {
				
			}
			
			/* 					TODO: integer-type var = lb
			 * 					TODO: random-access-iterator-type var = lb
			 * 					TODO: pointer-type var = lb
			 */ 
		}
		 
		return false;
	}
	
	public static boolean isConditionedConstantly(ForStatement loop) {
		//	for (init-expr; test-expr; incr-expr) structured-block
		final org.eclipse.jdt.core.dom.Expression testExp = loop.getConditionExpression();	// TODO: getCanonicalConditionOf(loop)
		if (ASTUtil.isBinaryRelation(testExp)) 
			return isRelatedConstantly((Assignment) testExp);
		
		return false;
	}
	
	public static boolean isRelatedConstantly(Assignment rel) {
		/* 		test-expr 	One of the following:
		 * 					var relational-op b
		 * 					b relational-op var
		 */
		return rel.getOperand1() instanceof IASTLiteralExpression 
				^ rel.getOperand2() instanceof IASTLiteralExpression;
	}

	

	public static boolean iteratesConstantly(ForStatement loop) {
		return increasesConstantly(loop.getExpression());
	}

	public static boolean increasesConstantly(org.eclipse.jdt.core.dom.Expression exp) {
		return ASTAssignableComputer.isUnaryAssignment(exp)  
				|| (exp instanceof Assignment && increasesConstantly((Assignment) exp));
	}
	
	public static boolean increasesConstantly(Assignment exp) {
		final org.eclipse.jdt.core.dom.Expression incrExp = exp.getOperand2();
		
		/* 					var += incr
		 * 					var -= incr
		 */
		if (ASTAssignableComputer.isAbbreviatedBinaryAssignment(exp)) 
			return ASTUtil.isConstant(incrExp);
		
		/* 					var = var + incr
		 *					var = incr + var
		 * 					var = var - incr
		 */
		else if (ASTAssignableComputer.isPlainBinaryAssignment(exp) && incrExp instanceof Assignment) {
			Assignment incrAdd = (Assignment) incrExp;
			// a constant (IASTLiteralExpression) has no name (Name)
			return ASTUtil.isConstant(incrAdd.getOperand1()) || 
					ASTUtil.isConstant(incrAdd.getOperand2());
		}
		
		return false;
	}

	
	
	/**
	 * Even there's no dependency between the loop body and updaters, side-effects may still vary by each loop round.
	 * Therefore dependency checking like the following is not necessary.
	 * <code>
	 * if (LValueComputer.getDependentOnBy(loop.getBody(), loop.updaters()) != null) ...
	 * </code> 
	 * 
	 * @param loop
	 * @param runTimeAddr
	 * @param condGen
	 * @return
	 */
	@SuppressWarnings({ "removal", "unchecked" })
    public static Map<org.eclipse.jdt.core.dom.Expression, ArithmeticExpression> getIncrementsOf(
            ForStatement loop, final ASTAddressable runTimeAddr, VODCondGen condGen) {
        final Map<org.eclipse.jdt.core.dom.Expression, ArithmeticExpression> increments = LOOP_INCREMENT_CACHE.computeIfAbsent(loop, key -> new HashMap<>());
        if (!increments.isEmpty()) {
            return increments;
        }
        
        for (org.eclipse.jdt.core.dom.Expression exp : (List<org.eclipse.jdt.core.dom.Expression>) loop.updaters()) {
            if (exp instanceof PrefixExpression) {
                final PrefixExpression uie = (PrefixExpression) exp;    // unary incr-expr
                final PrefixExpression.Operator op = uie.getOperator();
                if (op == PrefixExpression.Operator.DECREMENT) increments.put(exp, Int.MINUS_ONE);  // --var
                else if (op == PrefixExpression.Operator.INCREMENT) increments.put(exp, Int.ONE);   // ++var
                else DebugElement.throwTodoException("Unsupported prefix expression operator:" + op);
                
            } else if (exp instanceof PostfixExpression) {
                final PostfixExpression uie = (PostfixExpression) exp;    // unary incr-expr
                final PostfixExpression.Operator op = uie.getOperator();
                if (op == PostfixExpression.Operator.DECREMENT) increments.put(exp, Int.MINUS_ONE);  // var--
                else if (op == PostfixExpression.Operator.INCREMENT) increments.put(exp, Int.ONE);   // var++
                else DebugElement.throwTodoException("Unsupported postfix expression operator:" + op);
                
            } else if (exp instanceof Assignment) try {
                final Assignment asgm = (Assignment) exp;    // binary incr-expr
                final Assignment.Operator op = asgm.getOperator();
                final org.eclipse.jdt.core.dom.Expression bieRhs = asgm.getRightHandSide();
                
                if (op == Assignment.Operator.PLUS_ASSIGN)  // var += incr 
                    increments.put(exp, Elemental.getSkipNull(()-> (ArithmeticExpression) Expression.fromRecursively(bieRhs, runTimeAddr, condGen)));

                if (op == Assignment.Operator.MINUS_ASSIGN) // var -= incr 
                    increments.put(exp, Elemental.getSkipNull(()-> (ArithmeticExpression) Expression.fromRecursively(bieRhs, runTimeAddr, condGen).minus()));
                    
                if (op == Assignment.Operator.ASSIGN) { 
                    if (bieRhs instanceof InfixExpression) {
                        final InfixExpression asgr = (InfixExpression) bieRhs;    // assigner
                        final InfixExpression.Operator asgrOp = asgr.getOperator();
                        final org.eclipse.jdt.core.dom.Expression asgrLhs = asgr.getLeftOperand();
                        final org.eclipse.jdt.core.dom.Expression asgrRhs = asgr.getRightOperand();
                        final Name citName = ASTUtil.getNameOf(asgm.getLeftHandSide());
                        final Name asgrLhsName = ASTUtil.getNameOf(asgrLhs);
                        if (asgrOp == InfixExpression.Operator.PLUS) {
                            if (ASTUtil.equals(citName, asgrLhsName, true))                 // var = var + incr
                                increments.put(exp, Elemental.getSkipNull(()-> 
                                (ArithmeticExpression) Expression.fromRecursively(asgrRhs, runTimeAddr, condGen)));
                            if (ASTUtil.equals(citName, ASTUtil.getNameOf(asgrRhs), true))  // var = incr + var
                                increments.put(exp, Elemental.getSkipNull(()-> 
                                (ArithmeticExpression) Expression.fromRecursively(asgrLhs, runTimeAddr, condGen)));
                        } else if (asgrOp == InfixExpression.Operator.MINUS) { 
                            if (ASTUtil.equals(citName, asgrLhsName, true))                 // var = var - incr
                                increments.put(exp, Elemental.getSkipNull(()-> 
                                (ArithmeticExpression) Expression.fromRecursively(asgrRhs, runTimeAddr, condGen).minus()));
                            else 
                                DebugElement.throwTodoException("Unsupported minus assignment:" + asgrRhs);
                        }
                    } else 
                        DebugElement.throwTodoException("Unsupported assignment:" + bieRhs);
                }
            } catch (Exception e) {
                Elemental.throwUnhandledException(e);
            }
        }
        
        return increments;
    }

	public static Int getIncrementOf(ForStatement loop, Expression initializer, final ASTAddressable runTimeAddr, VODCondGen condGen) {
        if (loop == null) return null;
        
        final Map<Expression, ArithmeticExpression> increments = ASTLoopUtil.getIncrementsOf(loop, runTimeAddr, condGen);
        return initializer == null 
                ? increments.values().iterator().next() 
                : increments.get(initializer);
	}
	
	public static Int setIncrementOf(ForStatement loop, Int incr) {
		return LOOP_INCREMENT_CACHE.put(loop, incr);
	}



	public static NavigableSet<Statement> toNavigableSet(Collection<Statement> loops, VODCondGen condGen) {
		final NavigableSet<Statement> loopSet = 
				new TreeSet<>(new ASTRuntimeLocationComputer(condGen));
		loopSet.addAll(loops);
		return loopSet;
	}

}