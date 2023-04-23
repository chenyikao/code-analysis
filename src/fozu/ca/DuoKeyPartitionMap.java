/**
 * 
 */
package fozu.ca;

import java.util.Collections;
import java.util.EnumMap;
import java.util.Map;

/**
 * @author Kao, Chen-yi
 *
 */
public class DuoKeyPartitionMap<
K1 extends Partitionable<E1>, E1 extends Enum<E1>, 
K2 extends Partitionable<E2>, E2 extends Enum<E2>, V> 
extends DuoKeyMap<E1, E2, DuoKeyPartitionMap<K1, E1, K2, E2, V>> {

	private DuoKeyMap<K1, K2, V> partEndMap = null;
	
	public DuoKeyPartitionMap(Class<E1> key1Enum) {
		super(new EnumMap<>(key1Enum));
	}



	/**
	 * @param k1
	 * @param k2
	 * @return
	 */
	public V get(K1 k1, K2 k2) {
		if (k1 == null || k2 == null) return null;
		
		E1 pk1 = k1.nextPartitionKey(); 
		E2 pk2 = k2.nextPartitionKey(); 
		if (pk1 == null || pk2 == null) 
			return partEndMap == null ? null : partEndMap.get(k1, k2);
		
		DuoKeyPartitionMap<K1, E1, K2, E2, V> pm = super.get(pk1, pk2);
		return pm != null ? pm.get(k1, k2) : null;
	}

	
	
	/**
	 * @param k1
	 * @param k2
	 * @param v
	 * @return 
	 */
	@SuppressWarnings("unchecked")
	public V put(K1 k1, K2 k2, V v) {
		if (k1 == null || k2 == null) return null;
		
		E1 pk1 = k1.nextPartitionKey(); 
		E2 pk2 = k2.nextPartitionKey(); 
		if (pk1 == null || pk2 == null) {
			if (partEndMap == null) partEndMap = new DuoKeyMap<>();
			return partEndMap.put(k1, k2, v);
		}

		Map<E2, DuoKeyPartitionMap<K1, E1, K2, E2, V>> pk2Map = get(pk1);
		if (pk2Map == null) put(pk1, pk2Map = Collections.synchronizedMap(
						new EnumMap<>((Class<E2>) pk2.getClass())));
		
		DuoKeyPartitionMap<K1, E1, K2, E2, V> pm = pk2Map.get(pk2);
		if (pm == null) pm = new DuoKeyPartitionMap<>((Class<E1>) pk1.getClass());
		return pm.put(k1, k2, v);
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