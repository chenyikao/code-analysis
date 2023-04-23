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
	
	static public <T, C extends Collection<T>> Emptable from(C col) {
		return new EmptableCollection<>(col);
	}
	
	default public boolean isSemanticallyEmpty() {
		return isEmpty();
	}
	
}