/**
 * 
 */
package fozu.ca;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Predicate;

/**
 * @author Kao, Chen-yi
 *
 */
public class DuoKeyMap<K1, K2, V> extends Elemental implements Mappable<K1, Map<K2, V>> {

	private Map<K1, Map<K2, V>> key1Map = null;
	
	public DuoKeyMap() {
		this(new HashMap<>());
	}
	
	/**
	 * @param key1Map
	 */
	@SuppressWarnings("removal")
	protected DuoKeyMap(Map<K1, Map<K2, V>> key1Map) {
		if (key1Map == null) DebugElement.throwNullArgumentException("map of key1");
		this.key1Map = Collections.synchronizedMap(key1Map);
	}



	@SuppressWarnings("unchecked")
	final static public <K1, K2, V, M1 extends Map<K1, M2>, M2 extends Map<K2, V>> 
	DuoKeyMap<K1, K2, V> from(M1 map) {
		return new DuoKeyMap<>((Map<K1, Map<K2, V>>) map);
	}
	


	/**
	 * @param key1
	 * @return
	 */
	public boolean containsKey(K1 key1) {
		return key1Map.containsKey(key1);
	}
	
	/**
	 * @param key1
	 * @param key2
	 * @return
	 */
	public boolean containsKeys(K1 key1, K2 key2) {
		assert key1Map != null;
		Map<K2, V> key2Map = key1Map.get(key1);
		return key2Map != null && key2Map.containsKey(key2);
	}

	public boolean containsValue(K2 k2, V value) {
		for (Map<K2, V> key2Map : key1Map.values()) {
			if (k2 == null) {
				if (key2Map.containsValue(value)) return true;
			} else
				if (Elemental.tests(()-> key2Map.get(k2).equals(value))) return true;
		}
		return false;
	}
	
	
	
	public void clear() {
		key1Map.clear();
	}
	
	
	
	/**
	 * @return
	 */
	public boolean isEmpty() {
		assert key1Map != null;
		return key1Map.isEmpty();
	}
	
	

	/**
	 * @param k1
	 * @return
	 */
	public Map<K2, V> get(K1 k1) {
		return toMap().get(k1);
	}
	
	/**
	 * @param k1
	 * @param k2
	 * @return
	 */
	public V get(K1 k1, K2 k2) {
		Map<K2, V> key2Map = key1Map.get(k1);
		return key2Map != null 
				? key2Map.get(k2)
				: null;
	}



	/**
	 * @param k1
	 * @param key2Map
	 * @return 
	 */
	public Map<K2, V> put(K1 k1, Map<K2, V> key2Map) {
		return key1Map.put(k1, key2Map);
	}
	
	/**
	 * @param k1
	 * @param k2
	 * @param v
	 * @return 
	 */
	public V put(K1 k1, K2 k2, V v) {
		Map<K2, V> key2Map = key1Map.get(k1);
		
		if (key2Map == null) key1Map.put(
				k1, key2Map = Collections.synchronizedMap(new HashMap<K2, V>()));
		
		return key2Map.put(k2, v);
	}
	
	
	
	/**
	 * @param k1
	 * @param k2
	 * @return 
	 */
	public V remove(K1 k1, K2 k2) {
		Map<K2, V> key2Map = key1Map.get(k1);
		if (key2Map == null) return null;
		return key2Map.remove(k2);
	}
	


	/**
	 * @return
	 */
	public Set<K1> key1Set() {
		return key1Map.keySet();
	}

	public K1 key1For(K2 k2) {
		for (Entry<K1, Map<K2, V>> entry : key1Map.entrySet()) 
			if (entry.getValue().containsKey(k2)) return entry.getKey();
		return null;
	}

	

	/**
	 * @return
	 */
	public Set<K2> key2Set() {
		Set<K2> keys = new HashSet<>();
		for (Map<K2, V> key2Map : key1Map.values())
			// {@link Map#values()} doesn't support {@code add} or {@code addAll}
			keys.addAll(key2Map.keySet());
		return keys;
	}
	


	/**
	 * @return Maybe empty if there's no mapping for {@link K1}.
	 */
	public Collection<V> values() {
		// {@link Map#values()} doesn't support {@code add} or {@code addAll}
		Collection<V> values = new ArrayList<>();
		for (Map<K2, V> key2Map : key1Map.values())
			values.addAll(key2Map.values());
		return values;
	}
	
	/**
	 * For avoiding unnecessary (unconditional) value collecting.
	 * 
	 * @param condition
	 * @return Conditional values.
	 */
	public Collection<V> values(Predicate<V> condition) {
		if (condition == null) return values();
		
		// {@link Map#values()} doesn't support {@code add} or {@code addAll}
		Collection<V> values = new ArrayList<>();
		for (Map<K2, V> key2Map : key1Map.values())
			for (V v2 : key2Map.values())
				if (condition.test(v2)) values.add(v2);
		return values;
	}

	public Set<V> valueSet() {
		return new HashSet<>(values());
	}
	
	public Set<V> valueSet(Predicate<V> condition) {
		return new HashSet<>(values(condition));
	}



	/* (non-Javadoc)
	 * @see fozu.ca.vodcg.Mappable#toMap()
	 */
	@Override
	public Map<K1, Map<K2, V>> toMap() {
		return Collections.unmodifiableMap(key1Map);
	}

}