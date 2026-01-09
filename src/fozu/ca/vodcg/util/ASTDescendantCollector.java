/**
 * 
 */
package fozu.ca.vodcg.util;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;

/**
 * @author Kao, Chen-yi (Timmy)
 * 
 */
public class ASTDescendantCollector<T> extends ASTVisitor {
	
	private ASTNode parent;
	private Class<T> descendType;
	private boolean collectsOnlyChildren;
	private final List<T> descendants = new ArrayList<>();
	
	public ASTDescendantCollector(
			ASTNode parent, Class<T> descendType, boolean collectsOnlyChildren) {
		this.parent = parent;
		this.descendType = descendType;
		this.collectsOnlyChildren = collectsOnlyChildren;
	}
	
	public List<T> getDescendants() {
		return descendants;
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public void preVisit(ASTNode node) {
		if (descendType.isInstance(node)) {
			if (collectsOnlyChildren) {
				if (node.getParent() == parent) descendants.add((T) node);
			} else {
				descendants.add((T) node);
			}
		}
	}
    
}