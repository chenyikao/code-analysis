/**
 * 
 */
package fozu.ca;

/**
 * A linear double-key-single-value map list.
 * 
 * TODO: optimize list searching?
 * 
 * @author Kao, Chen-yi
 *
 */
public class DuoKeyMapList<K1, K2, V> extends MappableList<K1, MappableList<K2, V>.KeyValuePair> {
	
	final private MappableList<K2, V> K2V = new MappableList<K2, V>();
	
	

	@SuppressWarnings({ "removal" })
	public V get(K1 key1, K2 key2) {
		DebugElement.throwTodoException("k1-(k2, v) list?");
		MappableList<K2, V>.KeyValuePair k2V = get(key1);
		return k2V != null ? k2V.getValue() : null;
	}
	
	@SuppressWarnings({ "removal" })
	public V put(K1 key1, K2 key2, V value) {
		DebugElement.throwTodoException("k1-(k2, v) list?");
		MappableList<K2, V>.KeyValuePair pk2v = put(key1, K2V.pair(key2, value));
		return pk2v == null ? null : pk2v.getValue();
	}

}