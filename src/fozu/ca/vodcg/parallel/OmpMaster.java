/**
 * 
 */
package fozu.ca.vodcg.parallel;

import org.eclipse.jdt.core.dom.Statement;

import fozu.ca.vodcg.VODCondGen;
import fozu.ca.vodcg.condition.ParallelCondition;

/**
 * @author Kao, Chen-yi
 *
 */
public class OmpMaster extends OmpSingle {

	/**<q>
	 * There is no implied barrier associated with this directive.
	 * </q>
	 * 
	 * @param address
	 * @param blockStat
	 * @param pc
	 * @param condGen
	 * @see https://computing.llnl.gov/tutorials/openMP/#MASTER 
	 */
	private OmpMaster(/*IASTFileLocation address, */Statement blockStat, 
			ParallelCondition pc, VODCondGen condGen) {
		super(/*address, */blockStat, true, pc, condGen);
	}

//	/**
//	 * @param loc
//	 * @param stat
//	 * @param condGen
//	 * @return
//	 */
//	protected static OmpMaster from(
//			IASTFileLocation address, Statement blockStat, ParallelCondition pc, VODCondGen condGen) {
//		// TODO? cache objects of such type
//		return new OmpMaster(address, blockStat, pc, condGen);
//	}

}