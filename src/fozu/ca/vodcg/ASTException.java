/**
 * 
 */
package fozu.ca.vodcg;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.cdt.core.dom.ast.IProblemBinding;

import fozu.ca.vodcg.util.ASTUtil;

/**
 * @author Kao, Chen-yi
 *
 */
public class ASTException extends IllegalArgumentException {

	private static final long serialVersionUID = 1L;
	
	public ASTException(ASTNode node) {
		super("unsupported AST node " + ASTUtil.toStringOf(node));
	}
	
	public ASTException(IBinding bind, Throwable cause) {
		super("non-AST binding? " + bind, cause);
	}
	
//	public ASTException(IProblemBinding bind, Throwable cause) {
//		super("AST binding problem? " + bind + 
//				" " + ASTUtil.toStringOf(bind.getASTNode()), cause);
//	}

}