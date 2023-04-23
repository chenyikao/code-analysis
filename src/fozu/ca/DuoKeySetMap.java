/**
 * 
 */
package fozu.ca;

import java.util.Map;

/**
 * @author Kao, Chen-yi
 *
 */
public class DuoKeySetMap<Key, Value> extends DuoKeyMap<Key, Key, Value> {

	/**
	 * @param k1
	 * @param k2
	 * @return
	 */
	public Value get(Key k1, Key k2) {
		Map<Key, Value> key2Map = get(k1);
		if (key2Map != null) return key2Map.get(k2);

		key2Map = get(k2);
		if (key2Map != null) return key2Map.get(k1);
		else return null;
	}



	/**
	 * @param k1
	 * @param k2
	 * @param v
	 * @return 
	 */
	public Value put(Key k1, Key k2, Value v) {
		Map<Key, Value> key2Map = get(k1);

		if (key2Map != null) return key2Map.put(k2, v);
			
		key2Map = get(k2);
		if (key2Map != null) return key2Map.put(k1, v);
			
		assert key2Map == null;
		return super.put(k1, k2, v);
//		return super.put(k2, k1, v);	for saving memory
	}

}
