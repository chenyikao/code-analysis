/**
 * 
 */
package fozu.ca;

/**
 * @author Kao, Chen-yi
 *
 */
public class DuoKeySetMultiPartitionMap<K extends KB, KP extends KB, KB extends MultiPartitionable, V> 
extends DuoKeyMultiPartitionMap<K, K, KP, KB, V> {

//	/**
//	 * @param keyEnum
//	 */
//	public DuoKeySetMultiPartitionMap() {
//		super();
//	}

	public V get(K k1, K k2) {
		V v = super.get(k1, k2);
		return v == null ? super.get(k2, k1) : v;
	}

	/**
	 * @param k1
	 * @param k2
	 * @param v
	 * @return 
	 */
	public V put(K k1, K k2, V v) {
		super.put(k1, k2, v);
		return super.put(k2, k1, v);
	}

}