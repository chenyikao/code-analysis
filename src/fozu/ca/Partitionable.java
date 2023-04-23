/**
 * 
 */
package fozu.ca;

/**
 * @author Kao, Chen-yi
 *
 */
public interface Partitionable<E extends Enum<E>> {

	/**
	 * @return
	 */
	E nextPartitionKey();

}
