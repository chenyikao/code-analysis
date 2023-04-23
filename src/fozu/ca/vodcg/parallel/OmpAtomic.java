package fozu.ca.vodcg.parallel;

import org.eclipse.jdt.core.dom.Statement;

import fozu.ca.vodcg.VODCondGen;
import fozu.ca.vodcg.condition.ParallelCondition;

/**
 * @author Kao, Chen-yi
 *
 */
public class OmpAtomic extends OmpDirective {

	/**
	 * @param address
	 * @param blockStat
	 * @param condGen
	 */
	private OmpAtomic(/*IASTFileLocation address, */Statement blockStat, ParallelCondition pc, 
			VODCondGen condGen) {
		super(/*address, */blockStat, pc, condGen);
	}

	/**
	 * @param address
	 * @param blockStat
	 * @param condGen
	 * @return
	 */
	protected static OmpAtomic from(
			/*IASTFileLocation address, */Statement blockStat, ParallelCondition pc, VODCondGen condGen) {
		// TODO? cache objects of such type
		return new OmpAtomic(/*address, */blockStat, pc, condGen);
	}


	
//	@Override
//	protected Proposition cacheRaceAssertion() {
//		return null;
//	}
	
	@Override
	public boolean isAtomic() {
		return true;
	}
	
}