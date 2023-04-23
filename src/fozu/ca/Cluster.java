/**
 * 
 */
package fozu.ca;

import java.util.function.Supplier;

/**
 * Clustered by the {@link Supplier#toString()}'s prefix.
 *  
 * @author Kao, Chen-yi
 *
 */
abstract public class Cluster<T> {
	
	protected T kernel = null;
	
	public Cluster(T kernel) {
		if (kernel == null) DebugElement.throwNullArgumentException("kernel");
		this.kernel = kernel;
	}

	
	
	public T getKernel() {
		return kernel;
	}
	
	@SuppressWarnings("unchecked")
	public boolean equals(Object obj) {
		if (obj == null) return false;
		if (obj == this) return true;
		if (!(obj instanceof Cluster)) return false;
		
		try {
			return equals((Cluster<T>) obj);
		} catch (ClassCastException e) {
			return false;
		}
	}
	
	protected abstract boolean equals(Cluster<T> c2);

	@Override
	public int hashCode() {
		return hashCluster();
	}
	
	protected abstract int hashCluster();
	
}