/**
 * 
 */
package fozu.ca.vodcg.util;

import java.util.List;

import org.eclipse.jdt.core.dom.ASTNameCollector;
import org.eclipse.jdt.core.dom.ArrayInitializer;
import org.eclipse.jdt.core.dom.InfixExpression;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.IASTDeclarator;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.IASTFieldReference;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.IASTFunctionCallExpression;
import org.eclipse.jdt.core.dom.IASTIdExpression;
import org.eclipse.jdt.core.dom.IASTInitializerClause;
import org.eclipse.jdt.core.dom.IASTLiteralExpression;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.ParenthesizedExpression;
import org.eclipse.jdt.core.dom.PostfixExpression;
import org.eclipse.jdt.core.dom.PrefixExpression;
import org.eclipse.jdt.core.dom.IASTNameOwner;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ArrayAccess;
import org.eclipse.jdt.core.dom.Statement;
import org.eclipse.jdt.core.dom.VariableDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.core.dom.IASTUnaryExpression;
import org.eclipse.jdt.core.dom.ArrayType;
import org.eclipse.jdt.core.dom.Assignment;

import fozu.ca.DebugElement;
import fozu.ca.Elemental;
import fozu.ca.vodcg.ASTAddressable;
import fozu.ca.vodcg.ASTException;
import fozu.ca.vodcg.Assignable;
import fozu.ca.vodcg.VODCondGen;

/**
 * Comparing runtime locations between L-value's in AST expressions.
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public final class ASTAssignableComputer {

//	private IIndex projectIndex;

//	public LValueComputer() {
//		projectIndex = projIdx;
//	}
	
	/**
	 * @param lValue - variable probably used in some parameter to find out
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public static Expression getArgumentExpressionOf(Expression lValue) {
		List<ASTNode> ancestors = ASTUtil.getAncestorsOfUntil(
				lValue, ASTUtil.AST_FUNCTION_CALL_EXPRESSION);
		if (ancestors != null) {
			final int grandAncestorIndex = ancestors.size() - 1;
			final ASTNode grandAncestor = ancestors.get(grandAncestorIndex);
			if (grandAncestor instanceof MethodInvocation) {
				final List<Expression> args = (List<Expression>) ((MethodInvocation) grandAncestor).arguments();
				// excluding MethodInvocation and lValue itself
				for (int i = grandAncestorIndex - 1; i > 0; i--) {
					ASTNode ancestor = ancestors.get(i);
					if (args.contains(ancestor)) 
						return (Expression) ancestor;
				}
			}
		}

		return null;
	}

//	public static IASTIdExpression getIdExpressionOf(Name name) {
//		if (name == null) DebugElement.throwNullArgumentException("name");
//		return Elemental.getSkipException(()-> ASTUtil.getAncestorOfAsUnless(
//				name, 
//				ASTUtil.AST_ID_EXPRESSION, 
//				ASTUtil.AST_EXPRESSION, 
//				false));	
//	}
//	
//	public static Expression getNonIdExpressionOf(Name name) {
//		if (name == null) DebugElement.throwNullArgumentException("name");
//		return Elemental.getNonNullSupplier(
//				()-> (Expression) getIdExpressionOf(name).getParent());	
//	}
	


	/**
	 * Currently supporting l-value type expression: {@link IASTIdExpression} and 
	 * pointer in {@link IASTUnaryExpression}.
	 * 
	 * @param exp
	 * @return
	 */
	@SuppressWarnings("removal")
	public static Name getVariableNameOf(final Expression exp) {
//			throws ASTException {
		if (exp == null) return null;
		
		switch (exp.getNodeType()) {
		case ASTNode.MODULE_QUALIFIED_NAME:
		case ASTNode.QUALIFIED_NAME:
		case ASTNode.SIMPLE_NAME:
			return (Name) exp;
//			final Name vName = ((IASTIdExpression) clause).getName();
//			final IBinding vBind = vName.resolveBinding();
//			if (vBind instanceof IVariable) return vName;
//			if (vBind instanceof IProblemBinding) 
//				throw new ASTException((IProblemBinding) vBind, null);
			
		case ASTNode.BOOLEAN_LITERAL: 
		case ASTNode.CHARACTER_LITERAL: 
		case ASTNode.NULL_LITERAL: 
		case ASTNode.NUMBER_LITERAL: 
		case ASTNode.STRING_LITERAL: 
		case ASTNode.TYPE_LITERAL: 
			return null;
			
		case ASTNode.PREFIX_EXPRESSION: 
			return getVariableNameOf(((PrefixExpression) exp).getOperand());
			
		case ASTNode.POSTFIX_EXPRESSION: 
			return getVariableNameOf(((PostfixExpression) exp).getOperand());
				
		default:
			return DebugElement.throwTodoException("unsupported expression");
		}
	}
	
	/**
	 * @param exp
	 * @return
	 */
	public static VariableDeclaration getVariableNameOwnerOf(
			final Name exp) 
					throws ASTException {
		return (exp != null && getVariableNameOf(exp) != null) ? exp : null;
	}
	
	/**
	 * @param exp
	 * @return
	 */
	public static VariableDeclaration getVariableNameOwnerOf(
			final PrefixExpression exp) {
		return (exp != null) ? getVariableNameOwnerOf(exp.getOperand()) : null;
	}
	
//	/**
//	 * Currently supporting l-value type expression: {@link IASTIdExpression} and 
//	 * pointer in {@link IASTUnaryExpression}.
//	 * 
//	 * @param clause
//	 * @return
//	 */
//	public static IASTNameOwner getVariableNameOwnerOf(
//			final IASTInitializerClause clause) 
//					throws ASTException {
//		if (clause == null) return null;
//		
//		if (clause instanceof IASTIdExpression) 
//			return getVariableNameOwnerOf((IASTIdExpression) clause);
//		else if (clause instanceof IASTFieldReference) 
//			return (IASTFieldReference) clause;
//		else if (clause instanceof IASTLiteralExpression) 
//			return null;
//		else if (clause instanceof IASTUnaryExpression) 
//			return getVariableNameOwnerOf((IASTUnaryExpression) clause);
//		else if (clause instanceof IASTArraySubscriptExpression) 
//			return getVariableNameOwnerOf(((IASTArraySubscriptExpression) clause).getArrayExpression());
//			
//		return DebugElement.throwTodoException("unsupported clause");
//	}



	public static boolean isAssignment(Expression exp) {
		return isUnaryAssignment(exp) || isBinaryAssignment(exp);
	}

	public static boolean isAssignment(PrefixExpression exp) {
		if (exp == null) return false;
		
		final PrefixExpression.Operator op = exp.getOperator();
		return op.equals(PrefixExpression.Operator.DECREMENT) || op.equals(PrefixExpression.Operator.INCREMENT);
	}
	
	public static boolean isAssignment(PostfixExpression exp) {
		if (exp == null) return false;
		
		final PostfixExpression.Operator op = exp.getOperator();
		return op.equals(PostfixExpression.Operator.DECREMENT) || op.equals(PostfixExpression.Operator.INCREMENT);
	}
	
//	public static boolean isLikeAssignment(Expression exp) {
//		return exp instanceof IASTUnaryExpression 
//				&& isLikeAssignment((IASTUnaryExpression) exp);
//	}
//	
//	public static boolean isLikeAssignment(IASTUnaryExpression exp) {
//		final Expression ubExp = ASTUtil.unbracket(exp);
//		return ubExp == exp 
//				? isLikeUnbracketedAssignment(exp) 
//				: isLikeAssignment(ubExp);
//	}
//	
//	private static boolean isLikeUnbracketedAssignment(IASTUnaryExpression exp) {
//		if (exp instanceof IASTUnaryExpression) 
//			switch (((IASTUnaryExpression) exp).getOperator()) {
//			case IASTUnaryExpression.op_amper		: return true;	// assignment if passed-by-reference
//			};
//		return false;
//	}
	

	
//	public static boolean isAssignmentOf(IASTFunctionCallExpression exp, Assignable asn) {
//		if (asn == null) DebugElement.throwNullArgumentException("assignable");
//		return asn.isAssignment(exp);
//	}
	
	@SuppressWarnings("removal")
	public static boolean isAssignedIn(Expression assignedExp, Expression exp) {
		if (!isAssignment(exp)) return false; 
		if (exp == assignedExp) return true;
		
		switch (exp.getNodeType()) {
		case ASTNode.PREFIX_EXPRESSION:
			return ASTUtil.contains(((PrefixExpression) exp).getOperand(), assignedExp);
		case ASTNode.POSTFIX_EXPRESSION:
			return ASTUtil.contains(((PostfixExpression) exp).getOperand(), assignedExp);
		case ASTNode.INFIX_EXPRESSION: 
			return ASTUtil.contains(((InfixExpression) exp).getLeftOperand(), assignedExp);
		default:
			return DebugElement.throwTodoException("Unsupported expression?");
		}
	}
	
	/**
	 * @param assignedName
	 * @param exp
	 * @return
	 */
	public static boolean isAssignedIn(Name assignedName, Expression exp) {
		// A unary assignment has only one operand containing the given l-value
		return isUnaryAssignment(exp) 
//				|| isBinaryAssigningOf(clause, name)
				|| isAssignedIn(getNonIdExpressionOf(assignedName), exp);
	}
	
	public static boolean isAssigning(Name name) {
		return isUnaryAssignment(getNonIdExpressionOf(name)) 
				|| isBinaryAssigning(name);
	}
	
	public static boolean isAssigning(Expression exp) {
		return exp instanceof ArrayInitializer;
	}
	
	public static boolean isAssigningIn(Expression assigningExp, Expression exp) {
		return isUnaryAssignment(assigningExp) 
				|| isBinaryAssigningIn(assigningExp, exp);
	}

	
	
	/**
	 * @param lValue
	 * @param exp
	 * @return
	 */
	public static boolean isDirectlyAssignedIn(Name lValue, Expression exp) {
		// A unary assignment has only one operand containing the given l-value
		if (isUnaryAssignment(exp)) return true; 
		
		// usually lhs of a direct (non-function-call) assignment
		// lValue == null -> not a classical AST ID, e.g. a parameter declaration
		return lValue != null && isBinaryAssignedIn(lValue, exp);
	}
	
	public static boolean isDirectlyAssignedIn(Name lValue, VariableDeclaration init) {
//		final IASTDeclarator decl = (IASTDeclarator) ASTUtil.getAncestorOfAs(
//				lValue, new Class[] {IASTDeclarator.class}, false);
//		return decl != null 
//				&& decl.getName() == lValue 
//				&& decl.getInitializer() == init;
		return init != null 
				&& init.getName() == lValue;
	}
	
//	/**
//	 * TODO: checking if pointer + name = l-value
//	 * @param lValue
//	 * @param init
//	 * 
//	 * @return
//	 */
//	public static boolean isDirectlyAssignedIn(
//			Expression lValue, VariableDeclarationFragment init) {
//		if (init == null || lValue == null) return false;
//		
//		IASTDeclarator decl = (IASTDeclarator) init.getParent();
////		decl.getPointerOperators();
//		return ASTUtil.equals(decl.getName(), ASTUtil.getNameOf(lValue));	// node-location-aware
//	}

//	/**
//	 * Meaning in the right hand side of binary assignment or subject of unary assignment.
//	 * 
//	 * @param var - assumed a variable ID
//	 * @return
//	 */
//	public static boolean isAssigning(Name var) {
//		return isBinaryAssigning(var) || isUnaryAssigning(var);
//	}

	public static Boolean isAssigned(Name ref, final ASTAddressable dynaAddr, VODCondGen condGen) {
		return Assignable.from(ref, dynaAddr, condGen).isAssigned();
	}

	/**
	 * Variable assigned means the subject reference is:
	 * 	either as a variable in the left hand side of a binary assignment or in a unary assignment,
	 * 	or as a function parameter passed by reference (in pointer type * or &).
	 *   
	 * Expression.isLValue() -/-> Expression.getParent() is an assignment
	 * 
	 * @param lvExp - the subject variable/parameter reference in a valid l-value expression,
	 * 	already bypassed Name 
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public static boolean isAssigned(Expression lvExp) {
		if (lvExp == null) return false;
		
		ASTNode lvAsg = lvExp;
		while (true) {
			lvAsg = ASTUtil.getAncestorOfAsUnless(lvAsg, ASTUtil.AST_ASSIGNMENT_TYPES,
					new Class[] {Statement.class}, true);
			if (lvAsg == null) break;
			
			if (lvAsg instanceof VariableDeclaration)
				return isAssignedIn(lvExp, ((VariableDeclaration) lvAsg).getInitializer());
			
			switch (lvAsg.getNodeType()) {
			case ASTNode.PREFIX_EXPRESSION:
				return isAssignedIn(lvExp, ((PrefixExpression) lvAsg).getOperand());
			case ASTNode.POSTFIX_EXPRESSION:
				return isAssignedIn(lvExp, ((PostfixExpression) lvAsg).getOperand());
			case ASTNode.ASSIGNMENT:
				return isAssignedIn(lvExp, ((Assignment) lvAsg).getLeftHandSide());
			}
		}
		return isPassedByRef(lvExp);
	}

	/**
	 * @param init
	 * @param asgn
	 * @return true if {@code asgn} is assigned in {@code init}.
	 */
	@SuppressWarnings("removal")
	public static boolean isBinaryAssignedIn(Name asgn, VariableDeclaration init) {
		if (asgn == null) DebugElement.throwNullArgumentException("assignable");
		return isDirectlyAssignedIn(asgn, init);
	}
	
	/**
	 * @param lValue
	 * @param clause
	 * @return true if {@code lValue} is assigned in {@code clause}.
	 * 	Excluding non-assigned arguments of some assigned arrays, such as some <code>clause</code> of array[<code>lValue</code>] = ...
	 */
	@SuppressWarnings("removal")
	public static boolean isBinaryAssignedIn(Expression lValue, Assignment clause) {
		if (lValue == null) DebugElement.throwNullArgumentException("l-value");
//		if (!isBinaryAssignment(clause)) return false;
		
		final Expression lhsAsm = clause.getLeftHandSide();
		final ASTNode lvArray = ASTUtil.getAncestorOfAs(lValue, ASTUtil.AST_ARRAY_SUB_TYPE, true);
		
		// some <code>clause</code> of array[<code>lValue</code>] = ...
		if (lvArray != null 
				&& ASTUtil.hasAncestorAs(lvArray, lhsAsm, null) 
				&& ASTUtil.hasAncestorAs(lValue, ((ArrayAccess) lvArray).getIndex(), null)) 
			return false;
		
		return ASTUtil.hasAncestorAs(lValue, lhsAsm, null);
	}
	
//	public static boolean isBinaryAssigningOf(IASTInitializerClause clause, Name var) {
//		return clause == getNonIdExpressionOf(var) 
//				&& isBinaryAssigning(var);
//	}
	
	public static boolean isBinaryAssigning(Name name) {
		return isBinaryAssigningIn(name, null);
	}

	public static boolean isBinaryAssigningIn(Expression exp, Expression exp2) {
		ASTNode expParent = exp;
//		final boolean isnLv = !exp.isLValue();
		while (expParent != null) {
			expParent = expParent.getParent();
			if (isAbbreviatedBinaryAssignment(expParent) 
					|| (isPlainBinaryAssignment(expParent) && !isLValueOf(exp, (InfixExpression) expParent))) 
				if (exp2 == null || exp2 == expParent) return true;
		}
		return false;
	}
    
    
    
    public static boolean isUnaryAssignment(ASTNode node) {
    		switch (node.getNodeType()) {
    		case ASTNode.PREFIX_EXPRESSION:
    			return isAssignment((PrefixExpression) node);
    		case ASTNode.POSTFIX_EXPRESSION:
    			return isAssignment((PostfixExpression) node);
    		case ASTNode.PARENTHESIZED_EXPRESSION:
    			return isUnaryAssignment(((ParenthesizedExpression) node).getExpression());
    		}
        return false;
    }

//  public static boolean isUnaryAssigning(Name var) {
//      return isUnaryAssigned(var);
//  }

    public static boolean isBinaryAssignment(ASTNode initializerOrClause) {
        return isPlainBinaryAssignment(initializerOrClause) 
                || isAbbreviatedBinaryAssignment(initializerOrClause);
    }

	public static boolean isPlainBinaryAssignment(ASTNode initializerOrClause) {
		return (initializerOrClause instanceof Assignment 
				&& ((Assignment) initializerOrClause).getOperator() == Assignment.Operator.ASSIGN)
				|| initializerOrClause instanceof VariableDeclarationFragment;
	}

	public static boolean isAbbreviatedBinaryAssignment(ASTNode initializerOrClause) {
		if (initializerOrClause instanceof Assignment) {
			final Assignment.Operator op = ((Assignment) initializerOrClause).getOperator();
			if (op == Assignment.Operator.BIT_AND_ASSIGN
			        || op == Assignment.Operator.BIT_OR_ASSIGN
			        || op == Assignment.Operator.BIT_XOR_ASSIGN
			        || op == Assignment.Operator.DIVIDE_ASSIGN
			        || op == Assignment.Operator.LEFT_SHIFT_ASSIGN
			        || op == Assignment.Operator.MINUS_ASSIGN
			        || op == Assignment.Operator.PLUS_ASSIGN
			        || op == Assignment.Operator.REMAINDER_ASSIGN
			        || op == Assignment.Operator.RIGHT_SHIFT_SIGNED_ASSIGN
			        || op == Assignment.Operator.RIGHT_SHIFT_UNSIGNED_ASSIGN
			        || op == Assignment.Operator.TIMES_ASSIGN) 
			    return true;
		}
		
		return false;
	}
	
	public static boolean isConstantAssignment(InfixExpression exp) {
		return isPlainBinaryAssignment(exp) && ASTUtil.isConstant(exp.getOperand2());
	}

	@SuppressWarnings("removal")
	public static boolean isLValueOf(Expression exp, InfixExpression binary) {
		if (binary == null) DebugElement.throwNullArgumentException("binary");
		return binary.getOperand1().contains(exp);
	}
	
	public static boolean isRewritingAssignment(Expression exp) {
		// every unary and abbreviated binary assignment is rewriting to its (lhs) operand
		if (isUnaryAssignment(exp) || isAbbreviatedBinaryAssignment(exp)) return true;
		
		// lhs of a binary assignment not appearing in rhs is not rewriting to lhs
		if (isPlainBinaryAssignment(exp)) {
			InfixExpression asg = (InfixExpression) exp;
			return isRewritingAssignmentTo(asg, getVariableNameOf(asg.getOperand1()));
		}
		
		return false;	// neither unary nor binary assignments
	}

	/**<pre>
	 * Abbreviated binary assignment: var in lhs <-> rewriting (var in rhs but not in lhs <-> not rewriting);
	 * Plain binary assignment: var in both lhs and rhs <-> rewriting.
	 * 
	 * If the given var appears in the rhs of a binary (both plain and abbreviated) assignment BUT NOT in its lhs,
	 * then the var is NOT rewriting.
	 * <br>
	 * 
	 * @param exp - expression filtered as a binary assignment 
	 * @param var - may be in lhs, rhs or neither one of them
	 * @return
	 */
	public static boolean isRewritingAssignmentTo(InfixExpression exp, Name var) {
		if (exp == null || var == null) return false;
		
		// every unary is rewriting to its only operand
//	if (isUnaryAssignment(exp)) 
//		return ((IASTIdExpression) ((IASTUnaryExpression) exp).getOperand()).getName() == var;
		
		// var in lhs <-> rewriting
		if (isAbbreviatedBinaryAssignment(exp)) return ((Expression) var.getParent()).isLValue();
		
		// var in both lhs and rhs <-> rewriting
		if (isPlainBinaryAssignment(exp)) {
			ASTNameCollector varCol = new ASTNameCollector(var.toCharArray());
			Name[] lhsVars, rhsVars;
			
			exp.getOperand1().accept(varCol); lhsVars = varCol.getNames();
			exp.getOperand2().accept(varCol); rhsVars = varCol.getNames();
			if (lhsVars != null && rhsVars != null) 	// var in both lhs and rhs
				for (Name v : lhsVars) if (((Expression) v.getParent()).isLValue()) return true;
		}
		
		return false;
	}
	
	/**
	 * Every lhs var in a rewriting assignment is rewritingly assigned.
	 * ONLY rhs var's in a binary rewriting one are NOT assigned in one rewriting assignment.
	 * 
	 * @param var
	 * @return
	 */
	public static boolean isRewritinglyAssigned(Name var) {
		final Expression varAsg = (Expression) var.getParent().getParent();	// bypassing IASTIdExpression 
		return isUnaryAssignment(varAsg)
				|| ((varAsg instanceof InfixExpression) 
						&& isRewritingAssignmentTo((InfixExpression) varAsg, var));
	}

	

	public static boolean isIdExpressionWithNameOf(ASTNode exp, Name name) {
		if (exp == null || name == null) return false;
		
		return exp instanceof Name && ((Name) exp).equals(name);
	}
	
	
	
	/**<pre>
	 * A (sub-) array reference is still some memory address (for possibly writing) and different from 
	 * array content for reading only, which means that the reference expression (var ID) must start from 
	 * the left-most IASTArraySubscriptExpression or pointer expression and never be in the subscript arguments.
	 * 
	 * A sub-array reference is in the form of var[...]... (not just ID var), which means 
	 * the reference has fewer levels of subscripts than the array's declared dimension.
	 * <br>
	 * 
	 * @param arrayId
	 * @param exp - the initializer clause or expression that refers the array at some (reference) address
	 * @return
	 */
	public static boolean isArrayReferenceIn(Expression lValue, Expression exp) {
//		TODO: if (clause instanceof IASTInitializerList)...
//		TODO: if (clause instanceof IASTDesignatedInitializer)...
//		TODO: if (clause instanceof ICPPASTInitializerList)...
//		TODO: if (clause instanceof ICPPASTInitializerClause)...

		// the reference has fewer levels of subscripts than the array's declared dimension.
		if (exp.getExpressionType() instanceof ArrayType) {
			
			// the reference expression (var ID) must start from the left-most IASTArraySubscriptExpression 
			// or pointer expression and never be in the subscript arguments.
			ASTNode lvOp = lValue;
			while (lvOp != exp) {
				if (lvOp == null) return false;	// arrayId may be null
				lvOp = lvOp.getParent();
			}
			return true;
		}
		
		return false;
//		return getContinuousAncestorCount(arrayOp, IASTArraySubscriptExpression.class) < getDeclaredDim(arrayId);
	}



	/**
	 * Checking if the given variable is accessed (as a top level ID or reference) 
	 * via a function argument. 
	 * TODO (in a separated method): or indirectly accessed via a non-function pointer. 
	 * 
	 * @param lValue
	 * @return
	 */
	public static boolean isPassedByRef(Expression lValue) {
		// TODO: or indirectly used by a non-function pointer...
		Expression varArg = getArgumentExpressionOf(lValue);
		
		if (varArg != null) {
			// var (ID) must be at the top level of parameter (ID)
			// (sub-) array reference (var[...]... or just ID var), not array content 
			if (isArrayReferenceIn(lValue, varArg)) return true;
		}
		
		return false;
	}
	
}
