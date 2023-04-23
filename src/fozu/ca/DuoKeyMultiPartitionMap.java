/**
 * 
 */
package fozu.ca;

/**
 * @author Kao, Chen-yi
 *
 */
public class DuoKeyMultiPartitionMap
<K1 extends KB, K2 extends KB, KP extends KB, KB extends MultiPartitionable, V> 
extends MultiPartitionMap<KP, DuoKeyMultiPartitionMap<K1, K2, KP, KB, V>> {

	private DuoKeyMap<K1, K2, V> leaf = null;



	/**
	 * @param pk1
	 * @return non-null partition map
	 */
	@SuppressWarnings("unchecked")
	protected DuoKeyMultiPartitionMap<K1, K2, KP, KB, V> 
	getMap(MultiPartitionable.Key pk1, MultiPartitionable.Key pk2) {
		return pk1 == null 
				? (DuoKeyMultiPartitionMap<K1, K2, KP, KB, V>) getMap(pk2)
				: (DuoKeyMultiPartitionMap<K1, K2, KP, KB, V>) getMap(pk1).getMap(pk2);
	}



	/**
	 * @param k1
	 * @param k2
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public V get(K1 k1, K2 k2) {
		try {
			// instead of getMap(...), super.get(key) implies recursive key.nextPartitionKey()
			DuoKeyMultiPartitionMap<K1, K2, KP, KB, V> pm = super.get((KP) k1);
			if (pm != null) return pm.get(k1, k2);
			
			pm = super.get((KP) k2);
			if (pm != null) return pm.get(k1, k2);
		} catch (ClassCastException e) {}
		
		return leaf != null ? leaf.get(k1, k2) : null;
	}

	
	
	/**
	 * @param k1
	 * @param k2
	 * @param v
	 * @return 
	 */
	@SuppressWarnings("unchecked")
	public V put(K1 k1, K2 k2, V v) {
		try {
			// instead of getMap(...), super.get(key) implies recursive key.nextPartitionKey()
			DuoKeyMultiPartitionMap<K1, K2, KP, KB, V> pm = super.get((KP) k1);
			if (pm != null) return pm.put(k1, k2, v);
			
			pm = super.get((KP) k2);
			if (pm != null) return pm.put(k1, k2, v);
		} catch (ClassCastException e) {}
		
		if (leaf == null) leaf = new DuoKeyMap<>();
		return leaf.put(k1, k2, v);
	}



//	/**
//	 * @return
//	 */
//	public Set<K2> key2Set() {
//		Set<K2> keys = null;
//		for (Map<K2, V> key2Map : key1Map.values()) {
//			Set<K2> key2s = key2Map.keySet();
//			// {@link Map#values()} doesn't support {@code add} or {@code addAll}
//			if (keys == null) keys = Collections.synchronizedSet(key2s);
//			else keys.addAll(key2s);
//		}
//		return keys;
//	}
//	
//
//
//	/**
//	 * @return Maybe empty if there's no mapping for {@link K1}.
//	 */
//	public Collection<V> values() {
//		Collection<V> values = null;
//		for (Map<K2, V> key2Map : key1Map.values()) {
//			Collection<V> subValues = key2Map.values();
//			// {@link Map#values()} doesn't support {@code add} or {@code addAll}
//			if (values == null) values = Collections.synchronizedCollection(subValues);
//			else values.addAll(subValues);
//		}
//		return values;
//	}

}