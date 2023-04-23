/**
 * 
 */
package fozu.ca.vodcg.parallel;

import org.eclipse.jdt.core.dom.Statement;

import fozu.ca.DebugElement;
import fozu.ca.Elemental;

/**
 * @author Kao, Chen-yi
 *
 */
public interface ThreadPrivatizable {

	public Boolean isConstant();
	
	default public Statement getPrivatizingBlock() {
		return Elemental.tests(isConstant())
				? null
				: DebugElement.throwTodoException("unknown privatizing block");
	}
	
	default public boolean isThreadPrivate() {
		return getPrivatizingBlock() != null;
	}

}