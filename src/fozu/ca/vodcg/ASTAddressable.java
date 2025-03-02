/**
 * 
 */
package fozu.ca.vodcg;

import java.util.NavigableSet;

import org.eclipse.jdt.core.dom.ASTNode;

import fozu.ca.Addressable;
import fozu.ca.DebugElement;

/**
 * @author Kao, Chen-yi
 *
 */
public interface ASTAddressable extends Addressable {

	ASTAddressable cacheRuntimeAddress();
	
	ASTNode getASTAddress();
	
	default public ASTAddressable getRuntimeAddress() {
//		return isFrozen() 
//				? null 
//						: cacheRuntimeAddress();
		return cacheRuntimeAddress();
	}

	@Override
	default String getShortAddress() {
		return isInAST()
				? ASTUtil.toLocationOf(getASTAddress())
				: null;
	}

	@Override
	default <A extends Addressable> boolean equalsAddress(A address2) {
		return Addressable.super.equalsAddress(address2)
				|| (address2 instanceof ASTAddressable 
						&& getASTAddress() == ((ASTAddressable) address2).getASTAddress());
	}

//	default public boolean isFrozen() {
//		return isInAST() 
//				&& SystemElement.getNonNull(()-> getASTAddress().isFrozen());
//	}
	
	default boolean isInAST() {
		return getASTAddress() != null;
	}
	
	default public boolean isPreviousRuntimes(Addressable address2) {
		if (address2 == null) return SystemElement.throwNullArgumentException("address");
		return previousRuntimes().contains(address2);
	}
	
	/**
	 * @param <T>
	 * @return (TODO? non-null) set of previous candidate addressable's,
	 * 	which are navigable by their addresses, at run-time
	 */
	@SuppressWarnings("removal")
    default <T extends Addressable> NavigableSet<T> previousRuntimes() {
		return DebugElement.throwTodoException("unsupported runtime previous");
	}

}