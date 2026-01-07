/**
 * 
 */
package fozu.ca.vodcg.util;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.Name;

import fozu.ca.vodcg.ASTAddressable;
import fozu.ca.vodcg.Assignable;
import fozu.ca.vodcg.VODCondGen;

/**
 * @author Kao, Chen-yi (Timmy)
 * 
 */
public class ASTDependencyComputer extends ASTNodeFinder<Expression> {
	
	private Expression dependentOnBy = null;



	public ASTDependencyComputer(Expression exp) {
		super(exp);
	}
	
	/**
	 * An ID is said to be dependent on a loop only if it's a variable ID and the variable is either 
	 * the loop iterator or an array accessed (indexed) by the iterator through 
	 * the (subscript) arguments or pointer to the array.
	 *
	 * TODO: Supporting loops more than the canonical ones.
	 * 
	 * @param loop
	 * @param dynaAddr
	 * @param condGen
	 */
	public ASTDependencyComputer(ForStatement loop, final ASTAddressable dynaAddr, final VODCondGen condGen) {
		super(Assignable.fromCanonicalIteratorOf(loop, dynaAddr, condGen).toASTExpression());	// loop iterator
	}
	
	@Override
	public boolean preVisit2(ASTNode lValue) {
		final Expression exp = this.getVisitTarget();
		
		if (exp.equals(lValue)) 
			dependentOnBy = (Expression) lValue;
		
		if (exp instanceof Name && lValue instanceof Name 
				&& ASTUtil.equals((Name) exp, (Name) lValue, true))
			dependentOnBy = (Expression) lValue;
		
//		while (true) {
//			ASTNode lvParent = lValue.getParent();
//			if (lvParent == null) break;
//			if (lvParent instanceof Expression) {
//				// or an array accessed (indexed) by the loop iterator
//				// through the (subscript) arguments or pointer to the array.
//				if (((Expression) lvParent).getExpressionType() instanceof ArrayType) 
//					return getDependentOnBy(lValue);
//			} else break;
//		}

		return dependentOnBy == null;	// continue-ing to find dependentOnBy
	}
	
	/**
	 * @param lValue - assumed a variable name ID
	 * @return name-equally dependent expression
	 */
	public Expression getDependentOnBy(Expression lValue) {
		this.getVisitTarget().accept(this);
		return dependentOnBy;
	}
	
//	/**
//	 * @param exps - assumed expressions
//	 * @param lValue - assumed a variable ID that's probably used in the expressions
//	 * @return
//	 */
//	public Expression getDependentOnBy(ASTNode[] exps, Expression lValue) {
//		if (exps != null) for (ASTNode exp : exps) if (exp instanceof Expression) {
//			Expression by = getDependentOnBy((Expression)exp, lValue);
//			if (by != null) return by;
//			else return getDependentOnBy(exp.getChildren(), lValue);
//		}
//		return null;
//	}

}