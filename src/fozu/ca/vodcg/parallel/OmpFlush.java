package fozu.ca.vodcg.parallel;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.jdt.core.dom.Statement;

import fozu.ca.vodcg.VODCondGen;
import fozu.ca.vodcg.condition.ParallelCondition;

/**
 * @author Kao, Chen-yi
 *
 */
public class OmpFlush extends OmpFlushable {

	/**
	 * @param address
	 * @param blockStat
	 * @param condGen
	 */
	protected OmpFlush(/*IASTFileLocation address, */Statement blockStat, ParallelCondition pc,
			VODCondGen condGen) {
		super(/*address, */blockStat, false, pc, condGen);
	}

	/**
	 * @param clauses
	 * @param address
	 * @param blockStat
	 * @param condGen
	 * @return
	 */
	protected static OmpFlush from(String clauses, /*IASTFileLocation address, */Statement blockStat, 
			ParallelCondition pc, VODCondGen condGen) {
//		assert address != null;
		
		Matcher mFlush = Pattern.compile("("
				+ OmpUtil.patternParenthesizedList("list", null, null)	+ "|" + "\\s" + ")+")
				.matcher(clauses);
		
		OmpFlush of = new OmpFlush(/*address, */blockStat, pc, condGen);
		
		String fList = mFlush.group("list");
		if (fList != null) ;	// TODO
		return of;
	}


	
//	@Override
//	protected Proposition cacheRaceAssertion() {
//		return null;
//	}
	
}
