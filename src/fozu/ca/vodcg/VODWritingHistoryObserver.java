/**
 * 
 */
package fozu.ca.vodcg;

import java.util.SortedSet;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.Name;

/**
 * @author Kao, Chen-yi
 *
 */
public class VODWritingHistoryObserver extends ASTVisitor {

	/**
	 * @param wrs_ov - initial cache of writing references of OV
	 */
	public VODWritingHistoryObserver(SortedSet<Name> wrs_ov) {
		super(false);
		// TODO Auto-generated constructor stub
	}

	
	
	/**
	 * @param ov - observed variable, OV
	 * @param f - beginning function of observation
	 * @param observeSubcall - observing sub-function calls recursively or not
	 * @return
	 */
	public Iterable<Name> observe(Name ov, MethodDeclaration f, boolean observeSubcall) {
		f.accept(this);
		// TODO Auto-generated method stub
		return null;
	}



	public Iterable<Name> observe(Name ov, MethodDeclaration f) {
		// TODO: if ov is a pointer, return observe(ov, f, true);
		return observe(ov, f, false);
	}

}
