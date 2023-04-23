/**
 * 
 */
package fozu.ca;

import java.util.Collection;
import java.util.function.Supplier;

/**
 * @author Kao, Chen-yi
 *
 */
public class EmptableCollection<T> implements Emptable {

	private Collection<T> kernel = null;
	
	@SuppressWarnings("deprecation")
	public EmptableCollection(Collection<T> col) {
		if (col == null) DebugElement.throwNullArgumentException("collection");
		kernel = col;
	}
	
	static public <C extends Collection<T>, T> EmptableCollection<T> from(Supplier<C> colSup) {
		if (colSup == null) return null;
		
		final C col = colSup.get();
		return col == null
				? null
				: new EmptableCollection<>(col);
	}
	
	public Collection<T> getKernel() {
		return kernel;
	}
	
	@Override
	public boolean isEmpty() {
		return kernel.isEmpty();
	}

}