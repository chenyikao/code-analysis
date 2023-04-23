/**
 * 
 */
package fozu.ca;

import java.util.EnumMap;
import java.util.Map;

/**
 * @author Kao, Chen-yi
 *
 */
public interface MultiPartitionable {

	/**
	 * Partition key, different from map key.
	 * 
	 * Since Java doesn't support {@code new EnumMap<E.class>} for type parameter E.
	 * 
	 * @author Kao, Chen-yi
	 *
	 */
	public interface Key {

		<M extends Map<?, ?>> 		EnumMap<? extends Key, M> createPartitionMap();
		<M extends Mappable<?, ?>> 	EnumMap<? extends Key, M> createPartitionMappable();
		
	}

	default Key nextPartitionKey() {return null;}

}