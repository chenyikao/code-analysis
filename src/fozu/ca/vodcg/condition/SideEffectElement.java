/**
 * 
 */
package fozu.ca.vodcg.condition;

import fozu.ca.Emptable;

/**
 * @author Kao, Chen-yi
 *
 */
public interface SideEffectElement extends Emptable {
	
	default boolean isGuard() {
		return false;
	}
	
	default boolean suitsSideEffect() {
		return true;
	}

}