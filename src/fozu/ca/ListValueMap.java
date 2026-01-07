/**
 * 
 */
package fozu.ca;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * @author Kao, Chen-yi
 *
 */
public class ListValueMap<K, LV> extends Elemental {

	final private Map<K, List<LV>> map = new HashMap<>();
	

	
	/**
	 * @param key
	 * @return a non-null list of LV's
	 */
	public List<LV> get(K key) {
		return Elemental.get(()-> map.get(key),
				()-> Collections.emptyList());
	}
	
	
	
	public Set<K> keySet() {
		return map.keySet();
	}
	

	
	public LV put(K key, LV value) {
		List<LV> vl = map.get(key);
		if (vl == null) {
			vl = new ArrayList<LV>();
			map.put(key, vl);
		}
		final int pLast = vl.size() - 1;
		vl.add(value);
		return pLast == -1 ? null : vl.get(pLast);
	}

	
	
	@Override
	public String toString() {
		return map.toString();
	}
	
}