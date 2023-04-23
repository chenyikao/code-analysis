/**
 * 
 */
package fozu.ca.vodcg.parallel;

import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

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
	private OmpBarrier(IASTFileLocation address, IASTStatement blockStat, ParallelCondition pc, 
			VODCondGen condGen) {
		super(address, blockStat, pc, condGen);
		// TODO Auto-generated constructor stub
	}

	/**
	 * @param address
	 * @param blockStat
	 * @param condGen
	 * @return
	 */
	protected static OmpBarrier from(
			IASTFileLocation address, IASTStatement blockStat, ParallelCondition pc, VODCondGen condGen) {
		// TODO? cache objects of such type
		return new OmpBarrier(address, blockStat, pc, condGen);
	}

}