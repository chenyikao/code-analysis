/**
 * 
 */
package fozu.ca;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A key-value pair list implementing linear map access.
 * 
 * TODO: optimize list searching?
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class MappableList<K, V> implements Map<K, V>, Elemental {
	
	public class KeyValuePair extends Pair<K, V> {	// TODO: implements Entry<K, V>
		
		/**
		 * @param key
		 * @param value
		 */
		private KeyValuePair(K key, V value) {
			super(key, value);
		}
		
		/**
		 * @return
		 */
		public K getKey() {
			return getPeer1();
		}
		
		/**
		 * @return
		 */
		public V getValue() {
			return getPeer2();
		}
		
		public void setValue(V newValue) {
			setPeer2(newValue);
		}
		
	}



	final private List<KeyValuePair> list = new ArrayList<>();
	
	
	
	/* (non-Javadoc)
	 * @see java.util.Map#containsKey(java.lang.Object)
	 */
	@SuppressWarnings("unchecked")
	@Override
	public boolean containsKey(Object key) {
		try {
			return containsKey2((K) key);
		} catch (ClassCastException e) {
			return false;
		}
	}

	public boolean containsKey2(K key) {
		for (KeyValuePair li : list) if (li.getKey() == key) return true;
		return false;
	}
	
	/* (non-Javadoc)
	 * @see java.util.Map#containsValue(java.lang.Object)
	 */
	@Override
	public boolean containsValue(Object value) {
		DebugElement.throwTodoException("unimplemented Map method");
		return false;
	}


	
	public void clear() {
		list.clear();
	}
	
	/* (non-Javadoc)
	 * @see java.util.Map#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		return list.isEmpty();
	}


	
	/* (non-Javadoc)
	 * @see java.util.Map#get(java.lang.Object)
	 */
	@SuppressWarnings("unchecked")
	@Override
	public V get(Object key) {
		try {
			return get2((K) key);
		} catch (ClassCastException e) {
			return null;
		}
	}

	public V get2(K key) {
		for (KeyValuePair li : list) if (li.getKey() == key) return li.getValue();
		return null;
	}
	
	/* (non-Javadoc)
	 * @see java.util.Map#entrySet()
	 */
	@Override
	public Set<Entry<K, V>> entrySet() {
		DebugElement.throwTodoException("unimplemented Map method");
		return null;
	}
	
	/* (non-Javadoc)
	 * @see java.util.Map#keySet()
	 */
	@Override
	public Set<K> keySet() {
		DebugElement.throwTodoException("unimplemented Map method");
		return null;
	}
	
	/* (non-Javadoc)
	 * @see java.util.Map#values()
	 */
	@Override
	public Collection<V> values() {
		final List<V> vs = new ArrayList<>();
		for (KeyValuePair li : list) vs.add(li.getPeer2());
		return vs;
	}
	

	
	/**
	 * @param key
	 * @param value
	 * @return
	 */
	final public KeyValuePair pair(K key, V value) {
		put(key, value);
		for (KeyValuePair li : list) if (li.getKey() == key) return li;
		assert false; return null;
	}
	
	public V put(K key, V value) {
		for (KeyValuePair li : list) 
			if (li.getKey() == key) {
				V pv = li.getValue();
				if (pv != value) li.setValue(value); 
				return pv;
			}

		list.add(new KeyValuePair(key, value));
		return null;
	}

	/* (non-Javadoc)
	 * @see java.util.Map#putAll(java.util.Map)
	 */
	@Override
	public void putAll(Map<? extends K, ? extends V> m) {
		DebugElement.throwTodoException("unimplemented Map method");
	}

	/* (non-Javadoc)
	 * @see java.util.Map#remove(java.lang.Object)
	 */
	@Override
	public V remove(Object key) {
		DebugElement.throwTodoException("unimplemented Map method");
		return null;
	}

	public int size() {
		return list.size();
	}
	
}