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
public class OmpBarrier extends OmpFlush {

	/**
	 * @param address
	 * @param blockStat
	 * @param condGen
	 */
	private OmpBarrier(/*IASTFileLocation address, */Statement blockStat, ParallelCondition pc, 
			VODCondGen condGen) {
		super(/*address, */blockStat, pc, condGen);
	}

	/**
	 * @param address
	 * @param blockStat
	 * @param condGen
	 * @return
	 */
	protected static OmpBarrier from(
			/*IASTFileLocation address, */Statement blockStat, ParallelCondition pc, VODCondGen condGen) {
		// TODO? cache objects of such type
		return new OmpBarrier(/*address, */blockStat, pc, condGen);
	}

}