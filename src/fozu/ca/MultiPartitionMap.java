/**
 * 
 */
package fozu.ca;

import java.util.HashMap;
import java.util.Map;

import fozu.ca.MultiPartitionable.Key;

/**
 * @author Kao, Chen-yi
 *
 */
public class MultiPartitionMap<K extends MultiPartitionable, V> extends Elemental {

	private final 
	Map<Class<? extends Key>, Map<Key, MultiPartitionMap<K, V>>> 
	PARTITION_TABLE = new HashMap<>();
	
	/**
	 * The leaf map nodes in a hierarchical multi-partition tree
	 */
//	<LK extends Partitionable<E>, E extends Enum<E>> 
	private Map<K, V> leaf = null;
	
	
	
	/**
	 * @param pk
	 * @return non-null multi-partition map for non-null {@code pk}
	 */
	@SuppressWarnings({ "unchecked", "removal" })
	protected <PM extends Map<Key, MultiPartitionMap<K, V>>> 
	MultiPartitionMap<K, V> getMap(MultiPartitionable.Key pk) {
		if (pk == null) return null;
		
		Class<? extends Key> pkClass = pk.getClass();
		PM pm = (PM) PARTITION_TABLE.get(pkClass);
		if (pm == null) {
			pm = (PM) pk.<PM>createPartitionMap();
			if (pm == null) DebugElement.throwTodoException("Partition map not available!");
			PARTITION_TABLE.put(pkClass, pm);
		}
		
		MultiPartitionMap<K, V> pkm = pm.get(pk);
		if (pkm == null) pm.put(pk, pkm = new MultiPartitionMap<K, V>());
		return pkm;
	}



	/**
	 * @param key
	 * @return
	 */
	public V get(K key) {
		if (key == null) return null;
		
		Key pk = key.nextPartitionKey(); 
		if (pk == null) return leaf == null ? null : leaf.get(key);
		return getMap(pk).get(key);
	}

	
	
	/**
	 * @param key
	 * @param value
	 * @return 
	 */
	public V put(K key, V value) {
		if (key == null) return null;
		
		Key pk = key.nextPartitionKey(); 
		if (pk == null) {
			if (leaf == null) leaf = new HashMap<>();
			return leaf.put(key, value);
		}

		return getMap(pk).put(key, value);
	}

}