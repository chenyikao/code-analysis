/**
 * 
 */
package fozu.ca;

import java.util.EnumMap;
import java.util.Map;

/**
 * @author Kao, Chen-yi
 *
 */
public class PartitionMap<K extends Partitionable<E>, E extends Enum<E>, V> {

	private EnumMap<E, Map<K, V>> partitions = null;

	public PartitionMap(Class<E> keyEnum) {
		partitions = new EnumMap<>(keyEnum);
	}

	
	
	public V get(K key) {
		if (key == null) return null;
		
		Map<K, V> partition = partitions.get(key.nextPartitionKey());
		return partition == null ? null : partition.get(key);
	}
	
}