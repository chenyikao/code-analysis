/**
 * 
 */
package fozu.ca;

/**
 * A linear double-key-set-value map list.
 * 
 * TODO: optimize list searching?
 * 
 * @author Kao, Chen-yi
 *
 */
public class DuoKeySetMapList<K, V> extends DuoKeyMapList<K, K, V> {
	
	public V get(K key1, K key2) {
		V v = super.get(key1, key2);
		if (v != null) return v;
		return super.get(key2, key1);
	}
	
	public V put(K key1, K key2, V value) {
		V pv = super.put(key1, key2, value), pv2 = super.put(key2, key1, value);
		return pv == null ? pv2 : pv;
	}

}