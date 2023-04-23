/**
 * 
 */
package fozu.ca;

import java.util.Comparator;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class Pair<P1, P2> implements Comparator<Pair<P1, P2>> {
	
	private P1 peer1;
	private P2 peer2;
	
	public Pair() {
		this(null, null);
	}
	
	/**
	 * @param peer1
	 * @param peer2
	 */
	public Pair(P1 peer1, P2 peer2) {
		this.peer1 = peer1;
		this.peer2 = peer2;
	}
	
	/**
	 * @return
	 */
	public P1 getPeer1() {
		return peer1;
	}
	
	/**
	 * @return
	 */
	public P2 getPeer2() {
		return peer2;
	}

	
	
	/**
	 * @param newPeer1
	 * @return
	 */
	public P1 setPeer1(P1 newPeer1) {
		P1 old = peer1;
		peer1 = newPeer1;
		return old;
	}
	
	public P2 setPeer2(P2 newPeer2) {
		P2 old = peer2;
		peer2 = newPeer2;
		return old;
	}
	
	

	@SuppressWarnings("unchecked")
	@Override
	public int compare(Pair<P1, P2> p1, Pair<P1, P2> p2) {
		if (p1 == null || p2 == null) DebugElement.throwNullArgumentException("pair");
		
		int comp = 0;
		final P1 p1p1 = p1.peer1, p2p1 = p2.peer1;
		comp = p1p1 instanceof Comparator 
				? ((Comparator<P1>) p1p1).compare(p1p1, p2p1)
				: System.identityHashCode(p1p1) - System.identityHashCode(p2p1);
//		else DebugElement.throwTodoException("incomparable peer1");
		
		if (comp == 0) {
			final P2 p1p2 = p1.peer2, p2p2 = p2.peer2;
			if (p1p2 instanceof Comparator) return ((Comparator<P2>) p1p2).compare(p1p2, p2p2);
			else return System.identityHashCode(p1p2) - System.identityHashCode(p2p2);
//			else DebugElement.throwTodoException("incomparable peer2");
		}
		return comp;
	}
	
	public boolean equals(Object o2) {
		if (o2 == null) return false;
		if (o2 == this) return true;
		if (o2.getClass() != getClass()) return false;
		
		@SuppressWarnings("unchecked")
		Pair<P1, P2> pa2 = (Pair<P1, P2>) o2;
		P1 pa2p1 = pa2.peer1; 
		boolean eqPeer1 = peer1 == null ? pa2p1 == null : peer1.equals(pa2p1);
		P2 pa2p2 = pa2.peer2;
		boolean eqPeer2 = peer2 == null ? pa2p2 == null : peer2.equals(pa2p2);
		return eqPeer1 && eqPeer2;
	}
	
	public int hashCode() {
		final int prime = 31, p1hash = peer1 == null ? 0 : peer1.hashCode(),
				p2hash = peer2 == null ? 0 : peer2.hashCode();
		return prime * p1hash + p2hash;
	}
	
	

	public String toString() {
		return "(" + (peer1 == null ? "null" : peer1.toString()) + ", "
				+ (peer2 == null ? "null" : peer2.toString()) + ")";
	}

}