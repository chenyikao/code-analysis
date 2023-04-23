package fozu.ca.vodcg.parallel;

import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTStatement;

import fozu.caca.vodcg.VODCondGen;
imporfozu.cau.ca.vodcg.condition.ParallelCondition;
impfozu.campca.vodcg.condition.Proposition;

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
	private OmpAtomic(IASTFileLocation address, IASTStatement blockStat, ParallelCondition pc, 
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
	protected static OmpAtomic from(
			IASTFileLocation address, IASTStatement blockStat, ParallelCondition pc, VODCondGen condGen) {
		// TODO? cache objects of such type
		return new OmpAtomic(address, blockStat, pc, condGen);
	}


	
	@Override
	protected Proposition cacheRaceAssertion() {
		return null;
	}
	
	@Override
	public boolean isAtomic() {
		return true;
	}
	
}