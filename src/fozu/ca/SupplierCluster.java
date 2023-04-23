/**
 * 
 */
package fozu.ca;

import java.util.Comparator;
import java.util.function.Supplier;

public class SupplierCluster<T> extends Cluster<Supplier<T>> 
implements Addressable, Comparable<SupplierCluster<T>>, Comparator<SupplierCluster<T>> {

	/**
	 * @param kernel
	 */
	public SupplierCluster(Supplier<T> kernel) {
		super(kernel);
	}
	


	@Override
	public String getShortAddress() {
		return toStringCommatPrefix();
	}
	
	
	
	@Override
	public int compareTo(SupplierCluster<T> sc2) {
		return compare(this, sc2);
	}
	
	@SuppressWarnings("deprecation")
	@Override
	public int compare(SupplierCluster<T> sc1, SupplierCluster<T> sc2) {
		if (sc1 == null || sc2 == null) DebugElement.throwNullArgumentException("supplier cluster");
		
		return sc1.hashCluster() - sc2.hashCluster();
	}
	
	/* (non-Javadoc)
	 * @see fozu.ca.Cluster#equals(fozu.ca.Cluster)
	 */
	@Override
	protected boolean equals(Cluster<Supplier<T>> c2) {
		return c2 instanceof SupplierCluster 
				? getShortAddress().equals(((SupplierCluster<T>) c2).getShortAddress())
						: false;
	}
	
	protected int hashCluster() {
		return getShortAddress().hashCode();
	}



	public String toStringCommatPrefix() {
		final String str = kernel.toString();
		return str.substring(0, str.indexOf("@"));
	}

	public String toStringCommatSuffix() {
		final String str = kernel.toString();
		return str.substring(str.indexOf("@") + 1);
	}

}