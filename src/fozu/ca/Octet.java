/**
 * 
 */
package fozu.ca;

/**
 * @author Kao, Chen-yi
 *
 */
public class Octet<P1, P2, P3, P4, P5, P6, P7, P8> {
	private P1 peer1;
	private P2 peer2;
	private P3 peer3;
	private P4 peer4;
	private P5 peer5;
	private P6 peer6;
	private P7 peer7;
	private P8 peer8;
	
	public Octet(P1 peer1, P2 peer2, P3 peer3, P4 peer4, P5 peer5, P6 peer6, P7 peer7, P8 peer8) {
		this.peer1 = peer1;
		this.peer2 = peer2;
		this.peer3 = peer3;
		this.peer4 = peer4;
		this.peer5 = peer5;
		this.peer6 = peer6;
		this.peer7 = peer7;
		this.peer8 = peer8;
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
	 * @return
	 */
	public P3 getPeer3() {
		return peer3;
	}
	
	/**
	 * @return
	 */
	public P4 getPeer4() {
		return peer4;
	}
	
	/**
	 * @return
	 */
	public P5 getPeer5() {
		return peer5;
	}
	
	/**
	 * @return
	 */
	public P6 getPeer6() {
		return peer6;
	}
	
	/**
	 * @return
	 */
	public P7 getPeer7() {
		return peer7;
	}

	/**
	 * @return
	 */
	public P8 getPeer8() {
		return peer8;
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
	
	

	public String toString() {
		return "(" + (peer1 == null ? "null" : peer1.toString()) + ", "
				+ (peer2 == null ? "null" : peer2.toString()) + ", "
				+ (peer3 == null ? "null" : peer3.toString()) + ", "
				+ (peer4 == null ? "null" : peer4.toString()) + ", "
				+ (peer5 == null ? "null" : peer5.toString()) + ", "
				+ (peer6 == null ? "null" : peer6.toString()) + ", "
				+ (peer7 == null ? "null" : peer7.toString()) + ", "
				+ (peer8 == null ? "null" : peer8.toString()) + ")";
	}

}