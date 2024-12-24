/**
 * 
 */
package fozu.ca.vodcg.parallel;

import org.eclipse.jdt.core.dom.Statement;

import fozu.ca.vodcg.VODCondGen;
import fozu.ca.vodcg.condition.ParallelCondition;

/**
 * <q>THREADPRIVATE variables differ from PRIVATE variables (discussed later) because they are able 
 * to persist between different parallel regions of a code.</q><br>
 *  
 * <q>Data in THREADPRIVATE objects is guaranteed to persist only if the dynamic threads mechanism 
 * is "turned off" and the number of threads in different parallel regions remains constant. 
 * The default setting of dynamic threads is undefined.</q>
 * 
 * @see https://computing.llnl.gov/tutorials/openMP/#THREADPRIVATE
 * @author Kao, Chen-yi
 *
 */
public class OmpThreadPrivate extends OmpThreadPrivatizable {

	private OmpThreadPrivate(/*IASTFileLocation address, */Statement blockStat,
			ParallelCondition pc, VODCondGen condGen) {
		super(/*address, */blockStat, true, pc, condGen);
	}

//	/**
//	 * @param clauses
//	 * @param address
//	 * @param blockStat
//	 * @param condGen
//	 * @return
//	 */
//	protected static OmpThreadPrivate from(String clauses, IASTFileLocation address, 
//			Statement blockStat, ParallelCondition pc, VODCondGen condGen) {
//		assert clauses != null && address != null;
//		
//		OmpThreadPrivate otp = new OmpThreadPrivate(address, blockStat, pc, condGen);
//		otp.parseAndPrivatize(clauses);
//		return otp;
//	}

}