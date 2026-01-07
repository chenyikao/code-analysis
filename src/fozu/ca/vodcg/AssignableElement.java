/**
 * 
 */
package fozu.ca.vodcg;

import java.util.Optional;
import java.util.function.Supplier;

import fozu.ca.Elemental;
import fozu.ca.vodcg.condition.Expression;

/**
 * @author Kao, chen-yi
 *
 */
public interface AssignableElement {

	/**
	 * @return null if uncertain, like checking indirect argument assigned-ness during 
	 * AST parsing of function calls
	 */
	public default Boolean isAssigned() {
		return Elemental.tests(()-> getAssignable().isAssigned());
	}
	
	public default boolean isSelfAssigned() {
		return getAssigner() == this;
	}
	
//	default public boolean isInAST() {
//		return true;
//	}
	
	
	
	public static <T> T getAsn(Supplier<T> sup) {
		return getAsn(sup, ()-> null);
	}
	
	@SuppressWarnings({ "unchecked" })
	public static <T> T getAsn(Supplier<T> sup, Supplier<T> nullAlt) {
		try {
			return Elemental.getNonNullSupplier(sup);
			
		} catch (NullPointerException | ReenterException e) {	// may NOT be thrown directly from sup
			return (T) Optional.of(nullAlt)
					.orElseGet(() -> SystemElement.throwTodoException("non-assignable"));
			
		} catch (Exception e) {				// non-null exception with conditional halting
			return SystemElement.throwTodoException(e);
		}
	}
	
	public Assignable<?> getAssignable();
	
	/**
	 * @return null if not assigned.
	 */
	public default Expression getAssigner() {
		return Elemental.tests(isAssigned())
				? getAssignerIf()
				: null;
	}
	
	/**
	 * Should be invoked only if assigned.
	 * @return non-null
	 */
	default Expression getAssignerIf() {
		return getAsn(()-> getAssignable().getAssigner(),
				this::throwUnsupportedException);
	}
	
//	public AssignableElement previousAssigned();

	public default <T> T throwUnsupportedException() {
		return SystemElement.throwTodoException(
				"unsupported assignable element");
	}
	
}