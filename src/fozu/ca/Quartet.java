/**
 * 
 */
package fozu.ca;

/**
 * @author Kao, Chen-yi
 *
 */
public class Quartet<P1, P2, P3, P4> {

	private Pair<Pair<P1, P2>, Pair<P3, P4>> pair = null;
	
	/**
	 * @param peer1
	 * @param peer2
	 * @param peer3
	 * @param peer4
	 */
	public Quartet(P1 peer1, P2 peer2, P3 peer3, P4 peer4) {
		pair = new Pair<>(new Pair<>(peer1, peer2), new Pair<>(peer3, peer4));
	}

	public P1 getPeer1() {return pair.getPeer1().getPeer1();}
	public P2 getPeer2() {return pair.getPeer1().getPeer2();}
	public P3 getPeer3() {return pair.getPeer2().getPeer1();}
	public P4 getPeer4() {return pair.getPeer2().getPeer2();}

	public P1 setPeer1(P1 newPeer1) {return pair.getPeer1().setPeer1(newPeer1);}

	public String toString() {
		P1 p1 = getPeer1();
		P2 p2 = getPeer2();
		P3 p3 = getPeer3();
		P4 p4 = getPeer4();
		return "<" + p1 == null ? "null" : p1.toString() + ", " + 
				p2 == null ? "null" : p2.toString() + ", " +
				p3 == null ? "null" : p3.toString() + ", " +
				p4 == null ? "null" : p4.toString() + ">";
	}
	
}