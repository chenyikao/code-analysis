/**
 * 
 */
package fozu.ca;

/**
 * @author Kao, Chen-yi
 *
 */
public class Trio<P1, P2, P3> {

	private Pair<P1, Pair<P2, P3>> pair;
	
	/**
	 * @param peer1
	 * @param peer2
	 * @param peer3
	 */
	public Trio(P1 peer1, P2 peer2, P3 peer3) {
		pair = new Pair<>(peer1, new Pair<>(peer2, peer3));
	}
	
	
	
	public P1 getPeer1() {
		assert pair != null;
		return pair.getPeer1();
	}
	
	public P2 getPeer2() {
		assert pair != null;
		return pair.getPeer2().getPeer1();
	}

	public P3 getPeer3() {
		assert pair != null;
		return pair.getPeer2().getPeer2();
	}
	


	public P1 setPeer1(P1 newPeer1) {
		assert pair != null;
		return pair.setPeer1(newPeer1);
	}

	public P2 setPeer2(P2 newPeer2) {
		assert pair != null;
		return pair.getPeer2().setPeer1(newPeer2);
	}
	
	public P3 setPeer3(P3 newPeer3) {
		assert pair != null;
		return pair.getPeer2().setPeer2(newPeer3);
	}
	
}