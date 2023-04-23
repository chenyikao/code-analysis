/**
 * 
 */
package fozu.ca.vodcg.condition.version;

import fozu.ca.Elemental.TrySupplier;
import fozu.ca.vodcg.condition.Referenceable;

/**
 * @author Kao, Chen-yi
 *
 */
public interface AppendableVersion<Subject extends Referenceable> {

	public Version<Subject> append(TrySupplier<Version<Subject>, NoSuchVersionException> subVer);
	public Version<Subject> appendConstantCounting();
	
}