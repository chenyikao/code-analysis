/**
 * For avoiding infinite (direct or indirect) self traversal.
 * 
 * Using integer map of {@code Callee}s to handle structurally false traversal
 * reseting, such as subtract(...)-subtract_1(...)-subtract_2(...)-..., constantly.
 * 
 * TODO: {@link java.util.Stack} is inheriting-ly synchronized but has linear performance.
 */
package fozu.ca;

import java.util.HashMap;
import java.util.Map;

@SuppressWarnings("deprecation")
public class CalleeCache<Callee> {
	
	private final Map<Callee, Integer> cache = new HashMap<>();
	
	
	
	public void clear() {
		cache.clear();
	}
	
	/**
	 * @param callee
	 * @return 
	 */
	public Integer clear(Callee callee) {
		return cache.remove(callee);
	}
	
	/**
	 * @param callee
	 */
	public boolean contains(Callee callee) {
		if (callee == null) DebugElement.throwNullArgumentException("callee");
		return cache.containsKey(callee);
	}
	
	/**
	 * @return
	 */
	public boolean isEmpty() {
		return cache.isEmpty();
	}
	
	/**
	 * @param callee
	 */
	public Integer put(Callee callee) {
		if (callee == null) DebugElement.throwNullArgumentException("callee");
		
		Integer counts = cache.get(callee);
		if (counts == null) counts = 0;
		return cache.put(callee, ++counts);
	}
	
	/**
	 * @param callee
	 */
	public Integer remove(Callee callee) {
		if (callee == null) DebugElement.throwNullArgumentException("callee");
		
		Integer counts = cache.get(callee);
		if (counts == null) return null;
		else if (counts <= 0) DebugElement.throwInvalidityException("non-natural counts");
		else if (counts == 1) return cache.remove(callee);
		return cache.put(callee, --counts);
	}

//		public boolean remove(CallCache cache2) {
//			assert cache2 != null;
//			boolean result = false;
//			final DuoKeyMap<Object, Cluster<Supplier<?>>, Integer> c2 = cache2.cache;
//			for (Object caller2 : c2.key1Set()) 
//				for (Entry<Cluster<Supplier<?>>, Integer> callee2 
//						: c2.get(caller2).entrySet()) 
//					result |= remove(caller2, callee2.getKey().kernel) != null;
//			return result;
//		}
}