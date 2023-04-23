/**
 * 
 */
package fozu.ca;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class TrioValueMap<K, V1, V2, V3> implements Elemental {

	final private Map<K, Trio<V1, V2, V3>> map = new HashMap<>();
	

	
	public Trio<V1, V2, V3> get(K key) {
		return map.get(key);
	}
	
	public V1 getValue1(K key) {
		try {
			return Elemental.getSkipNull(()-> get(key).getPeer1());
		} catch (Exception e) {
			return DebugElement.throwUnhandledException(e);
		}
	}
	
	public V2 getValue2(K key) {
		try {
			return Elemental.getSkipNull(()-> get(key).getPeer2());
		} catch (Exception e) {
			return DebugElement.throwUnhandledException(e);
		}
	}

	public V3 getValue3(K key) {
		try {
			return Elemental.getSkipNull(()-> get(key).getPeer3());
		} catch (Exception e) {
			return DebugElement.throwUnhandledException(e);
		}
	}
	
	
	
	public Set<K> keySet() {
		return map.keySet();
	}
	

	
	public V1 put(K key, V1 value1) {
		return putValue1(key, value1);
	}
	
	public Trio<V1, V2, V3> put(K key, V1 value1, V2 value2, V3 value3) {
		Trio<V1, V2, V3> old = map.get(key);
		if (old == null) {
			old = new Trio<V1, V2, V3>(value1, value2, value3);
			map.put(key, old);
			return null;
		} else 
			return new Trio<>(old.setPeer1(value1), old.setPeer2(value2), old.setPeer3(value3));
	}

	/**
	 * @param key
	 * @param value1
	 * @return
	 */
	public V1 putValue1(K key, V1 value1) {
		Trio<V1, V2, V3> vs = map.get(key);
		if (vs == null)
			return put(key, value1, null, null).getPeer1();
		else 
			return vs.setPeer1(value1);
	}
	
	public V2 putValue2(K key, V2 value2) {
		Trio<V1, V2, V3> vs = map.get(key);
		if (vs == null)
			return put(key, null, value2, null).getPeer2();
		else 
			return vs.setPeer2(value2);
	}
	
	public V3 putValue3(K key, V3 value3) {
		Trio<V1, V2, V3> vs = map.get(key);
		if (vs == null)
			return put(key, null, null, value3).getPeer3();
		else 
			return vs.setPeer3(value3);
	}

}