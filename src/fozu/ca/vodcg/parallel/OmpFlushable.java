package fozu.ca.vodcg.parallel;

import org.eclipse.jdt.core.dom.Statement;

import fozu.ca.vodcg.VODCondGen;
import fozu.ca.vodcg.condition.ParallelCondition;

/**<q>
 * The FLUSH directive is implied for the directives shown in the table below. 
 * The directive is not implied if a NOWAIT clause is present.
 * 
 * C / C++:
 * 
    barrier
    parallel - upon entry and exit
    critical - upon entry and exit
    ordered - upon entry and exit
    for - upon exit
    sections - upon exit
    single - upon exit
    </q> 
    
 * @author Kao, Chen-yi
 * @see https://computing.llnl.gov/tutorials/openMP/#FLUSH
 *
 */
public abstract class OmpFlushable extends OmpDirective {
	
	private boolean noWait = false;
	
	protected OmpFlushable(/*IASTFileLocation address, */Statement blockStat, 
			boolean nowait, ParallelCondition pc, VODCondGen condGen) {
		super(/*address, */blockStat, pc, condGen);
		noWait = nowait;
	}
	
	

	/**
	 * The directive is not implied if a NOWAIT clause is present.
	 * @return
	 */
	public boolean canFlush() {
		return !getNowait();
	}
	
	public boolean isSynchronized() {
		return !getNowait();
	}
	
	public final boolean getNowait() {
		return noWait;
	}

//	protected Set<PathVariablePlaceholder> getArrayEnclosersLike(PathVariablePlaceholder arrayEncloser) {
//		assert arrayEncloser != null;
//		final Set<PathVariablePlaceholder> aes = new HashSet<>();
//		for (Assignable<?> asn : Assignable.fromOf(
//				getStatement(), arrayEncloser.getASTName(), cacheRuntimeAddress(), getCondGen()))
//			aes.add(asn.getPathVariablePlaceholder());
//		return aes;
//	}
	
	protected final void setNowait() {
		noWait = true;
	}
	
//	/**
//	 * @param parallelRegion
//	 */
//	protected void setParallelRegion(OmpParallel parallelRegion) {
//		super.setParallelRegion(parallelRegion);
//		parallelRegion.add(this);
//	}

}