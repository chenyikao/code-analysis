/**
 * 
 */
package fozu.ca;

import fozu.ca.condition.SerialFormat;

/**
 * @author Kao, Chen-yi
 *
 */
public interface Addressable {

	String getShortAddress();

	default String getIDSuffix(SerialFormat format) {
		return getShortAddress(format);
	}
	
	default String getShortAddress(SerialFormat format) {
		return getShortAddress();
	}
	
	default <A extends Addressable> boolean equalsAddress(A a2) {
		return a2 != null 
				&& (a2 == this 
				|| getShortAddress().equals(a2.getShortAddress()));
	}
	
	default public boolean derives(Addressable address2) {
		return equalsAddress(address2);
	}
	
	/**
	 * @return null if no previous addressable elements for sure
	 * TODO? throws Exception if the previous is unknown since a previous addressable is usually a complex structure
	 * to debug.
	 */
	default <T extends Addressable> T previous() {return null;}
	
}