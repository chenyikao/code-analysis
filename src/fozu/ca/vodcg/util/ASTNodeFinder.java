/**
 * 
 */
package fozu.ca.vodcg.util;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;

/**
 * @author Kao, Chen-yi (Timmy)
 * 
 */
public class ASTNodeFinder<T> extends ASTVisitor {
	private boolean hasFoundNode = false;
	private T target = null;
	
	public ASTNodeFinder(T visitTarget) {
		super();
		setVisitTarget(visitTarget);
//		shouldVisitStatements = true;
	}

	@Override
	public boolean preVisit2(ASTNode node) {
		if (node == target) {
			hasFoundNode = true;
			return false;	// stop visiting children of node
		}
		return true;	// continue-ing to find node
	}
	
//	@Override
//	protected int genericLeave(ASTNode node) {
//		if (findsIn && node == n) return PROCESS_ABORT;
//		return PROCESS_CONTINUE;	// continue-ing to find r if findsNextTo
//	}
	
	public boolean hasFoundNode() {
		return hasFoundNode;
	}
	
	public T getVisitTarget() {
		return this.target;
	}
	
	public void setVisitTarget(T visitTarget) {
		this.target = visitTarget;
	}
	
}