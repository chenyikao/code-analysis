/**
 * 
 */
package fozu.ca.vodcg.util;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.ReturnStatement;

import fozu.ca.DebugElement;

/**
 * @author Kao, Chen-yi (Timmy)
 * 
 */
public class ASTReturnCollector extends ASTVisitor {
	private boolean findsIn = false;
	private boolean findsNextTo = false;
	final protected List<ReturnStatement> result = new ArrayList<>();

	public ASTReturnCollector() {
		super();
	}
	
	@SuppressWarnings("removal")
	public List<ReturnStatement> findIn(ASTNode node) {
		if (node == null) DebugElement.throwNullArgumentException("AST node");
		
		final MethodDeclaration f = ASTUtil.getWritingFunctionDefinitionOf(node);
		if (f == null) DebugElement.throwNullArgumentException("function child");
//		findsIn = true; 
		f.accept(this);
		return result;
	}
	
	@SuppressWarnings("removal")
	public ReturnStatement findNextTo(ASTNode node) {
		if (node == null) DebugElement.throwNullArgumentException("AST node");
		
		final MethodDeclaration f = ASTUtil.getWritingFunctionDefinitionOf(node);
		if (f == null) return null;		// node is global
		
		f.accept(this);
		return result.isEmpty() ? null : result.get(0);
	}
	
	@Override
	public boolean visit(ReturnStatement statement) {
		result.add(statement);
		if (findsNextTo()) return false;	// stop visiting further
		return true;	// continue-ing to find n
	}
	
	public boolean findsIn() {
		return findsIn;
	}
	
	public boolean findsNextTo() {
		return findsNextTo;
	}

	public void setFindsIn(boolean findsIn) {
		this.findsIn = findsIn;
	}
	
	public void setFindsNextTo(boolean findsNextTo) {
		this.findsNextTo = findsNextTo;
	}
	
}