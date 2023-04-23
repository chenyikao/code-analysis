/**
 * For avoiding infinite (direct or indirect) self traversal.
 * 
 * Using integer map of {@code Callee}s to handle structurally false traversal
 * reseting, such as subtract(...)-subtract_1(...)-subtract_2(...)-..., constantly.
 * 
 * TODO: {@link java.util.Stack} is inheriting-ly synchronized but has linear performance.
 */
package fozu.ca;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

@SuppressWarnings("deprecation")
public class CallCache<Caller, Callee> {
	
	private final Map<Caller, CalleeCache<Callee>> cache = 
			Collections.synchronizedMap(new HashMap<>());
	
	
	
	/**
	 * 
	 */
	public void clear() {
		cache.clear();
	}
	
	/**
	 * @param caller
	 * @param callee
	 */
	public boolean contains(Caller caller, Callee callee) {
		if (caller == null) DebugElement.throwNullArgumentException("caller");
		if (callee == null) DebugElement.throwNullArgumentException("callee");
		
		return cache.containsKey(caller) && cache.get(caller).contains(callee);
	}
	
	/**
	 * @return
	 */
	public boolean isEmpty() {
		return cache.isEmpty();
	}
	
	/**
	 * @param caller
	 * @param callee
	 */
	public Integer put(Caller caller, Callee callee) {
		assert caller != null && callee != null;
		
		CalleeCache<Callee> cc = cache.get(caller);
		if (cc == null) cache.put(caller, cc = new CalleeCache<>());
		return cc.put(callee);
	}
	
	/**
	 * @param caller
	 * @param callee
	 */
	public Integer remove(Caller caller, Callee callee) {
		assert caller != null && callee != null;
		
		CalleeCache<Callee> cc = cache.get(caller);
		return cc == null ? null : cc.remove(callee);
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