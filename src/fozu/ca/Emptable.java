/**
 * 
 */
package fozu.ca;

import java.util.Collection;

/**
 * @author Kao, Chen-yi
 *
 */
public interface Emptable {

	boolean isEmpty();
	
	public static <T, C extends Collection<T>> Emptable from(C col) {
		return new EmptableCollection<>(col);
	}
	
	public default boolean isSemanticallyEmpty() {
		return isEmpty();
	}
	
}