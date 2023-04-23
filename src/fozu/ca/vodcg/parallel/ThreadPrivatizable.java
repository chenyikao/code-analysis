/**
 * 
 */
package fozu.ca.vodcg.parallel;

import org.eclipse.cdt.core.dom.ast.IASTStatement;

import fozu.ca.DebugElement;
import fozu.ca.Elemental;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public interface ThreadPrivatizable {

	public Boolean isConstant();
	
	default public IASTStatement getPrivatizingBlock() {
		return Elemental.tests(isConstant())
				? null
				: DebugElement.throwTodoException("unknown privatizing block");
	}
	
	default public boolean isThreadPrivate() {
		return getPrivatizingBlock() != null;
	}

}