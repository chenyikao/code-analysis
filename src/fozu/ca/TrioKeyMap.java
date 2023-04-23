/**
 * 
 */
package fozu.ca;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * @author Kao, Chen-yi
 *
 */
public class TrioKeyMap<Key1, Key2, Key3, Value> {

	private Map<Key1, DuoKeyMap<Key2, Key3, Value>> key1Map = new HashMap<>();
	
	
	
	/**
	 * @return
	 */
	public Set<Key1> key1Set() {
		return key1Map.keySet();
	}
	
	/**
	 * @return
	 */
	public Set<Key2> key2Set() {
		Set<Key2> key2s = new HashSet<>();
		for (DuoKeyMap<Key2, Key3, Value> k2k3Map : key1Map.values())
			key2s.addAll(k2k3Map.key1Set());
		return key2s;
	}
	
	public Key2 key2For(Key3 k3) {
		for (DuoKeyMap<Key2, Key3, Value> k2k3Map : key1Map.values()) {
			final Key2 k2 = k2k3Map.key1For(k3);
			if (k2 != null) return k2;
		}
		return null;
	}
	


	/**
	 * @param k1
	 * @param k2
	 * @param k3
	 * @return
	 */
	public Value get(Key1 k1, Key2 k2, Key3 k3) {
		DuoKeyMap<Key2, Key3, Value> key2key3Map = key1Map.get(k1);
		if (key2key3Map != null) return key2key3Map.get(k2, k3);
		else return null;
	}
	
	public Map<Key3, Value> get(Key1 k1, Key2 k2) {
		DuoKeyMap<Key2, Key3, Value> key2key3Map = key1Map.get(k1);
		if (key2key3Map != null) return key2key3Map.get(k2);
		else return null;
	}



	public boolean isEmpty() {
		return key1Map.isEmpty();
	}
	

	
	/**
	 * @param k1
	 * @param k2
	 * @param k3
	 * @param v
	 */
	public void put(Key1 k1, Key2 k2, Key3 k3, Value v) {
		DuoKeyMap<Key2, Key3, Value> key2key3Map = key1Map.get(k1);
		if (key2key3Map == null) key1Map.put(k1, key2key3Map = new DuoKeyMap<Key2, Key3, Value>());
		
		key2key3Map.put(k2, k3, v);
	}

}
