package fozu.ca.solver;

import java.io.IOException;
import java.util.AbstractList;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Stack;

import fozu.ca.DebugElement;

/**<pre>
 * Treating multiple parameters waiting for range-degrading-solving 
 * as a multi-digit continuously counting number.
 * 
 * Taking 3-parameter triples (p1/digit1, p2/digit2, p3/digit3) for example:
 * (LB1,     (p1,    (LB1,         (p1,      (LB1 + 1,      (p1,      (UB1,     (p1,      (UB1,    (p1,      (UB1,
 *  LB2,  ... p2, ... LB2 + 1,  ... p2,   ... MIN,       ... p2,   ... MIN,  ... p2,   ... UB2, ... p2,   ... UB2,
 *  LB3)      p3)     MIN)          p3)       MIN)           p3)       MIN)      p3        MIN)     p3        UB3)
 * 
 * Range tags: ;RangeDegradeIn,LB,UB,MAX,MIN,Param(1,2,...)
 * 
 * TODO Z3 range predicate assumption:
 * 	1)fixed and ordered two-layer pattern - ... LBparam1 LBparam2 ... LBparamN {UBparam1 UBparam2 ... UBparamN} ))\n ;
 * 	2)only primitive integers for range parameters
 * 	3)inclusive range parameters
 * </pre>
 * @author Kao, Chen-yi
 *
 */
public class CarryInRangeDegrader extends DegraderChecker<CarryInRangeDegrader.CheckRange> {

	private static final String RANGE_DEGRADE_TYPE_CANT_BE_NULL = "Range degrade type can't be null!";
	private static final String TAG_PREFIX = ";RangeDegrade";

	private static Parameter defaultParam = null;
	private static int[] ParamMin;

	public enum Type {UB, LB, In};
	
	enum ParamOperation {ADD, MULTI};
	public static class Parameter extends fozu.ca.Parameter {
		protected String min;
		protected String max;

		public Parameter(String name, fozu.ca.condition.Type type, 
				final String MIN, final String MAX) {
			super(name, type);
			min = MIN;
			max = MAX;
		}
	}
	
	/**
	 * TODO: replacing this by {@link Parameter}.
	 * 
	 * @author Kao, Chen-yi
	 *
	 */
	protected static class Parameters implements Comparable<long[]>{
		
		private long[] values;
		private int dim;	// number of range parameters 

		Parameters(long[] params) {
			this.dim = params.length;
			this.values = Arrays.copyOf(params, dim);
		}
		

		
		/**
		 * Default addition for adding to the last significant digit.
		 * @param addend
		 * @return
		 */
		public Parameters add(long addend) {
			return add(addend, 1);
		}
		
		public Parameters add(long addend, int involveDigits) {
			Parameters sum = new Parameters(values);
			if (addend != 0 && involveDigits > 0) operateWithCarryIn(ParamOperation.ADD, addend, involveDigits, sum.values);
			return sum;
		}
		
		public Parameters multi(long multiplicand) {
			Parameters product = new Parameters(values);
			if (multiplicand != 1) operateWithCarryIn(ParamOperation.MULTI, multiplicand, dim, product.values);
			return product;
		}
		
		public Parameters divide(long dividend) {
			Parameters quotient = new Parameters(values);
			if (dividend != 1 && dividend != 0)
				for (int i = 0; i < dim; i++) {
					if (values[i] == 0) quotient.values[i] = -1;
					else if (values[i] < 0) quotient.values[i] *= dividend;
					else quotient.values[i] /= dividend;
				}
			return quotient;
		}

		public Parameters expMean(Parameters params2, int degradeInDegree) {
			if (this.equals(params2)) return params2;
			assert(dim == params2.dim);
			
			Parameters mean = new Parameters(values);
			long[] values2 = params2.values;
			int i;
			
			for (i = 0; i < dim; i++) {
				long diffValue = Math.abs(values[i] - values2[i]);
				// for faster (exponential) shrinking than halving
				mean.values[i] = Math.min(values[i], values2[i]);
				if (diffValue > 1) do {
					if (degradeInDegree == 0) degradeInDegree = 1;	// degradeInDegree != 0 => degDevider != 1 => m.v != v, v2
					long degDevider = (long)Math.pow(10, degradeInDegree);
					if (degDevider != 0) {
						mean.values[i] += Math.max(1, diffValue/degDevider);	// v < m.v < v2 for non-adjacent (v, v2)
						break;
					}
					degradeInDegree+=10;
				} while (true);
			}
			
			// Considering carry-in for such a expMean((1,MAX),(2,MIN)) =/= (1,MIN+)
			if (!((this.isLessThanOrEqualTo(mean) && mean.isLessThanOrEqualTo(params2)) 
					|| (params2.isLessThanOrEqualTo(mean) && mean.isLessThanOrEqualTo(this)))) 
				for (i = 0; i < dim-1; i++) 
					if (values[i] != values2[i]) {
						// pre-condition: newValues[i] == min(values[i], values2[i]) && newValues[i+1] >= min(values[i+1], values2[i+1])
						//					&& diffValue > 1
						mean.values[i]++;
						for (i++; i < dim; i++) mean.values[i] = Long.MIN_VALUE;
						// post-condition: newValues[i+1] > max(values[i+1], values2[i+1])
					}
			
			return mean;
		}
		


		/**
		 * Carry-in mechanism.
		 * @param op
		 * @param addend
		 * @param involveDigits
		 * @param targetDigits
		 */
		private void operateWithCarryIn(ParamOperation op, long addend, int involveDigits, long[] targetDigits) {
			assert(targetDigits.length == dim);
			
			int i;
			for (i = dim - involveDigits; i < dim; i++) switch (op) {
			case ADD: targetDigits[i] += addend; break;
			case MULTI: targetDigits[i] = (targetDigits[i] == 0) ? 1 : targetDigits[i]*addend; break;
			}

			// Carry-in propagation check
			for (i = dim - 1; i >= 0; i--) {
				if ((addend > 0 && targetDigits[i] < values[i]) 
						|| (addend < 0 && targetDigits[i] > values[i])) {
					if (i == 0) {targetDigits[0] = values[0]; break;}
					targetDigits[i-1] += ((addend > 0) ? 1 : -1);
				} 
			} 
		}

		@Override
		public int compareTo(long[] params2) {
			assert(dim == params2.length);
			
			for (int i = 0; i < dim; i++)
				if (values[i] != params2[i]) return Long.compare(values[i], params2[i]);
			return 0;
		}
		
		/* (non-Javadoc)
		 * @see java.lang.Object#equals(java.lang.Object)
		 */
		@Override
		public boolean equals(Object obj) {
			return this.compareTo(((Parameters)obj).values) == 0;
		}

		public boolean isLessThan(Parameters params2) {
			return compareTo(params2.values) < 0;
		}

		public boolean isLessThanOrEqualTo(Parameters params2) {
			return isLessThan(params2) || equals(params2);
		}

		public static Parameters min(Parameters p1,	Parameters p2) {
			return (p1.isLessThan(p2)) ? p1 : p2;
		}

		public static Parameters max(Parameters p1,	Parameters p2) {
			return (p1.isLessThan(p2)) ? p2 : p1;
		}

		public String toString() {
			String literal = "(";
			for (long param : values) literal += (String.valueOf(param) + ",");
			literal = literal.substring(0,literal.length()-1) + ")";
			return literal;
		}

	}
	
	/**
	 * @author Kao, Chen-yi
	 *
	 */
	protected class CheckRange extends Degrading {
		private Type type;
		private Parameters upperBound, lowerBound;
		
		/**
		 * Setting type with parsing and initializing the range parameters.
		 * @param type
		 */
		CheckRange(Type type) {
			// TODO (type != null);	
			this.type = type;
			// Parsing upper/lower bound(s) to initialize range parameters
			parseRange();
		}

		/**
		 * Setting type with parsing and initializing the range parameters.
		 * @param type Type in literal.
		 */
		CheckRange(String type) {
			assert(type != null);
			
			switch (type) {
			case "UB": this.type = Type.UB; break;
			case "LB": this.type = Type.LB; break;
			case "In": this.type = Type.In; break;
			default: throw new IllegalArgumentException("Illegal range degrade type: " + type);
			}
			parseRange();
		}
		
		/**
		 * Setting type given range parameters.
		 * @param type
		 * @param cilbound
		 * @param ciubound
		 */
		public CheckRange(Type type, Parameters cilbound, Parameters ciubound) {
			switch (type) {
			case In: 
			case UB: 
				// TODO if (ubound == null) throw ...
				upperBound = ciubound; 
				if (type == Type.UB) {this.type = Type.UB; break;}
			case LB:
				// TODO if (lbound == null) throw ...
				lowerBound = cilbound; 
				this.type = type; 
				break;
			default: throw new IllegalArgumentException("Illegal range degrade type: " + type);
			}
		}
		
		/**
		 * Quickly setting UB/LB or point type given only necessary range parameters.
		 * @param type
		 * @param bound
		 */
		public CheckRange(Type type, Parameters bound) {
			switch (type) {
			case In:  
			case UB: upperBound = bound; if (type == Type.UB) break;
			case LB: lowerBound = bound; break;
			default: throw new IllegalArgumentException("Illegal quick type: " + type);
			}
			this.type = type;
		}

		CheckRange(Type type, long[] bound) {
			this(type, new Parameters(bound));
		}
		
		CheckRange(Type type, long[] lbound, long[] ubound) {
			this(type, new Parameters(lbound), new Parameters(ubound));
		}

		

		public Parameters getLowerBound() {
			return new Parameters(lowerBound.values);
		}

		public Parameters getUpperBound() {
			return new Parameters(upperBound.values);
		}

		public CheckRange getConnectingRange() {
			Parameters lbound = lowerBound, ubound = upperBound;
			switch (type) {
			case In: 
			case UB: ubound = ubound.add(1); if (type == Type.UB) break;
			case LB: lbound = lbound.add(-1);
			}
			return new CheckRange(type, lbound, ubound);
		}

		/**
		 * @return
		 * @throws IOException 
		 */
		public String check() throws IOException {
			return Solver.z3check(checkFormulae);
		}

		public void parseRange() {
			switchTag(type);
			
			int intTokenIndex = rangePredTokens.length - 1, i;
			switch (type) {
			case In: 
			case UB: 
				// TODO tagLimit = TAG_PREFIX + "MIN";
				upperBound = new Parameters(new long[noParams]); 
				for (i = noParams - 1; i >= 0; i--, intTokenIndex--)
					upperBound.values[i] = Long.valueOf(rangePredTokens[intTokenIndex]);
				if (type == Type.UB) break;
			case LB: 
				// TODO tagLimit = TAG_PREFIX + "MAX";
				lowerBound = new Parameters(new long[noParams]); 
				for (i = noParams - 1; i >= 0; i--, intTokenIndex--)
					lowerBound.values[i] = Long.valueOf(rangePredTokens[intTokenIndex]);
				// if (this.type == Type.LB) break;
			}
		}

		public boolean isAPoint() {
			return (lowerBound != null) && (lowerBound.equals(upperBound));
		}
		
		public boolean precedes(CheckRange rng2) {
			assert(type != null && rng2.type != null);
			
			switch (type) {
			case UB:
				switch (rng2.type) {
				case UB: 
				case LB: return upperBound.isLessThan(rng2.lowerBound);
				case In: 
				}
			case In:
				switch (rng2.type) {
				case UB: return upperBound.isLessThan(rng2.upperBound);
				case In: return lowerBound.isLessThan(rng2.lowerBound) 
						|| (lowerBound.equals(rng2.lowerBound) && upperBound.isLessThan(rng2.upperBound));
				case LB:
				}
			case LB:
				switch (rng2.type) {
				case LB: 
				case In: return lowerBound.isLessThan(rng2.lowerBound);
				case UB: return false;
				}
			}
			// Should NOT reach here!
			return false;
		}
		
		public boolean intersects(CheckRange rng2) {
			assert(type != null && rng2.type != null);
			
			switch (type) {
			case UB:
				switch (rng2.type) {
				case UB: return true;
				case In: 
				case LB: return rng2.lowerBound.isLessThanOrEqualTo(upperBound);
				}
			case In:
				switch (rng2.type) {
				case UB: return lowerBound.isLessThanOrEqualTo(rng2.upperBound);
				case LB: 
				case In: 
					boolean rng2lbCond = rng2.lowerBound.isLessThanOrEqualTo(upperBound);
					if (type == Type.LB) return rng2lbCond;
					return rng2lbCond && !rng2.upperBound.isLessThan(lowerBound);
				}
			case LB:
				switch (rng2.type) {
				case LB: return true;
				case In: 
				case UB: return !rng2.upperBound.isLessThan(lowerBound);
				}
			}
			// Should NOT reach here!
			return false;
		}
		
		public boolean intersectsOrIsAdjacentTo(CheckRange rng2) {
			return intersects(rng2.getConnectingRange());
		}
		
		public List<CheckRange> merge(List<CheckRange> rngs) {
			List<CheckRange> result = new ArrayList<CheckRange>();
			
			if (rngs == null || rngs.isEmpty()) {result.add(this); return result;}
			
			// Categorizing ranges to merge
			List<CheckRange> ubs = new ArrayList<CheckRange>();
			List<CheckRange> ins = new ArrayList<CheckRange>();
			List<CheckRange> lbs = new ArrayList<CheckRange>();
			switch (type) {
			case UB: ubs.add(this); break;
			case In: ins.add(this); break;
			case LB: lbs.add(this); break;
			}
			for (CheckRange rng : rngs) 
				switch (rng.type) {
				case UB: ubs.add(rng); break;
				case In: ins.add(rng); break;
				case LB: lbs.add(rng); break;
				}
			
			int i; CheckRange rng, rng2;
			// Merging in-bounds
			if (!ins.isEmpty()) {
				for (i = 0;	i < ins.size(); i++) {
					rng = ins.get(i);
					for (int j = i + 1; j < ins.size(); j++) {
						rng2 = ins.get(j);
						if (rng.intersectsOrIsAdjacentTo(rng2)) {
							// The result is guaranteed sorted 
							ins.add(i, new CheckRange(Type.In, 
									Parameters.min(rng.lowerBound, rng2.lowerBound), 
									Parameters.max(rng.upperBound, rng2.upperBound)));
							ins.remove(i+1); 
							ins.remove(j);
							i = -1; break;
						}
					}
				}
//				ins.sort();
			}
			
			Parameters lbound, ubound; int boundIndex;
			// Merging upper and in-bounds
			if (!ubs.isEmpty()) {
				for (i = 1, boundIndex = 0, ubound = ubs.get(0).upperBound; i < ubs.size(); i++) {
					rng = ubs.get(i);
					if (!rng.upperBound.isLessThan(ubound)) {
						ubound = rng.upperBound; ubs.remove(boundIndex); boundIndex = i;}
					else ubs.remove(i);
				}
				if (!ins.isEmpty())
					for (i = 0, rng = ubs.get(0); i < ins.size(); i++) {
						rng2 = ins.get(i);
						if (rng.intersectsOrIsAdjacentTo(rng2)) {
							ins.remove(i); rng.upperBound = Parameters.max(rng.upperBound, rng2.upperBound);}
					}
			}
			
			// Merging lower and in-bounds
			if (!lbs.isEmpty()) {
				for (i = 1, boundIndex = 0, lbound = lbs.get(0).lowerBound; i < lbs.size(); i++) {
					rng = lbs.get(i);
					if (rng.lowerBound.isLessThan(lbound)) {
						lbound = rng.lowerBound; lbs.remove(boundIndex); boundIndex = i;}
					else lbs.remove(i);
				}
				if (!ins.isEmpty())
					for (i = ins.size() - 1, rng = lbs.get(0); i >= 0; i--) {
						rng2 = ins.get(i);
						if (rng.intersectsOrIsAdjacentTo(rng2)) {
							ins.remove(i); rng.lowerBound = Parameters.min(rng.lowerBound, rng2.lowerBound);}
					}
			}
			
			result.addAll(ubs);
			result.addAll(ins);
			result.addAll(lbs);
			return result;
		}

		public String toString() {
			return toString(true);
		}

		public String toString(boolean printsAscendingly) {
			switch (type) {
			case In: 
				if (isAPoint()) return lowerBound.toString();
				return (printsAscendingly)? lowerBound + "~" + upperBound : upperBound + "~" + lowerBound;
			case UB: 
				return (printsAscendingly)? "~" + upperBound : upperBound + "~";
			case LB: 
				return (printsAscendingly)? lowerBound + "~" : "~" + lowerBound;
			default:	// Should NOT reach here
				return null;
			}
		}

		@Override
		protected String degradeFormulae() {
			// TODO Auto-generated method stub
			return null;
		}

	}
	
	
	
	/**
	 * @author Kao, Chen-yi
	 *
	 */
	protected class RangeList extends AbstractList<CheckRange> {

		// Iterator for printing; descending iterator for merging new range 
		private List<CheckRange> ranges = new ArrayList<CheckRange>();

		/**
		 * Automatically merging and sorting after adding.
		 * 
		 * @see java.util.AbstractList#add(java.lang.Object)
		 */
		@Override
		public boolean add(CheckRange newRng) {
			if (ranges.isEmpty()) return ranges.add(newRng);
			
			List<CheckRange> overlappingRngs = new ArrayList<CheckRange>();
			int i = ranges.size() - 1, insIndex = i + 1;
			// Checking overlapping ranges
			for (;i >= 0; i--) {
				CheckRange existingRng = ranges.get(i);
				boolean isPreceding = newRng.precedes(existingRng);
				// replacing the range position if preceding, setting before i's changed below
				if (isPreceding) insIndex = i;
				if (newRng.intersectsOrIsAdjacentTo(existingRng)) {
					overlappingRngs.add(existingRng);
					ranges.remove(i);
					insIndex = i;
				}
				if (!isPreceding) break;
			}
			// Merging overlapping ranges and the result is guaranteed sorted since ALL overlapping parts are combined
			return ranges.addAll(insIndex, newRng.merge(overlappingRngs));
		}

		public boolean add(Parameters pointRng) {
			return add(new CheckRange(Type.In, pointRng, pointRng));
		}
		
		@Override
		public CheckRange get(int index) {
			return ranges.get(index);
		}

		/* (non-Javadoc)
		 * @see java.util.AbstractCollection#contains(java.lang.Object)
		 */
		@Override
		public boolean contains(Object o) {
			if (!(o instanceof CheckRange)) return false;
			for (CheckRange rng : ranges) if (rng.intersects((CheckRange)o)) return true;
			return false;
		}
		
		public void sort() {
			for (int i = 0;	i < ranges.size(); i++) {
				CheckRange rng = ranges.get(i);
				for (int j = i + 1; j < ranges.size(); j++) {
					CheckRange rng2 = ranges.get(j);
					if (!(rng.precedes(rng2) || rng.equals(rng2))) {
						ranges.remove(j);
						ranges.add(i, rng2);
						i = -1; break;
					}
				}
			}
		}

		@Override
		public int size() {
			return ranges.size();
		}

		@Override
		public Iterator<CheckRange> iterator() {
			return ranges.iterator();
		}

		/* (non-Javadoc)
		 * @see java.util.AbstractCollection#toString()
		 */
		@Override
		public String toString() {
			if (ranges.isEmpty()) return null;
			
			String result = "";
			for (int i = ranges.size() - 1; i >= 0; i--) result += ranges.get(i).toString(false);
			return result;
		}
	}
	
	
	
	private String formulae;
	
	private int noParams = -1;	// number of range parameters 
	private int noDegradeInParam;
	private int degradeInDegree;
	
	private String currentTag;
	private int currentTagIndex;
	private int argLastIndex;
	private Type lastType = null;
	private String checkFormulae;
	private String prePredFormulae;
	private String argRestFormulae;
	private String[] rangePredTokens;
	
	private String[] paramNames;	// number of parameters is fixed after initialization
	private Stack<CheckRange> checkRanges = new Stack<CheckRange>();
	private RangeList satRanges = new RangeList();
	private RangeList unsatRanges = new RangeList();
	private RangeList timeoutRanges = new RangeList();
	// TODO private String tagLimit;

	private CarryInRangeDegrader(String formulae) {
		// Counting the number of range parameters at initialization:
		currentTag = TAG_PREFIX + "Params";
		currentTagIndex = formulae.indexOf(currentTag);
		if (currentTagIndex == -1) throw new NoSuchElementException();
		
		this.formulae = formulae.replaceFirst(currentTag, "");	// nearly ready to check and needing no restoration
		String[] paramTokens = formulae.substring(currentTagIndex, formulae.indexOf("))", currentTagIndex)).split("\\s+");
		paramNames = Arrays.copyOfRange(paramTokens, 2, paramTokens.length);
		noDegradeInParam = noParams = paramNames.length;

//		TODO for (noParams = 1; ; noParams++) {
//			int paramIndex = formulae.indexOf(TAG_PREFIX + "Param" + noParams);
//			if (paramIndex == -1) {noParams--; break;}
//			
//			int pNameIndex = formulae.lastIndexOf("declare-fun ", paramIndex) + "declare-fun ".length();
//			paramNames.add(formulae.substring(pNameIndex, formulae.indexOf(" ", pNameIndex)));
//		}
//		noDegradeInParam = noParams;
		
		ParamMin = new int[noParams];
		for (int i = 0; i < noParams; i++) ParamMin[i] = 0;	// TODO: configurable via SMT formulae
	}
		
	/**
	 * @param formulae
	 * @param type
	 * @throws IllegalArgumentException
	 */
	public CarryInRangeDegrader(String formulae, Type type) throws IllegalArgumentException {
		this(formulae);
		
		if (type == null) throw new IllegalArgumentException(RANGE_DEGRADE_TYPE_CANT_BE_NULL);
		checkRanges.push(new CheckRange(type));
		//switchTag(type); done in the first time calling of nextCheck()
	}

	public CarryInRangeDegrader(String formulae, String type) throws IllegalArgumentException {
		this(formulae);
		
		if (type == null) throw new IllegalArgumentException(RANGE_DEGRADE_TYPE_CANT_BE_NULL);
		checkRanges.push(new CheckRange(type));
		//switchTag(type); done in the first time calling of nextCheck()
	}



	public static boolean isParam(String paramName) {
		return defaultParam != null
				&& defaultParam.getPeer1().equals(paramName);
	}
	
	public static void setParam(Parameter defaultParam) {
		CarryInRangeDegrader.defaultParam = defaultParam;
	}
	
	
	
	static final public String getTagMin() {
		return TAG_PREFIX + "MIN";
	}

	static final public String getTagMax() {
		return TAG_PREFIX + "MAX";
	}
	
	static final public String getTagParam() {
		return TAG_PREFIX + "Param";
	}
	

	
	@SuppressWarnings("removal")
    @Override
	public CheckRange getCurrentDegrading() {
		return DebugElement.throwTodoException("current degrading");
	}

	public String getCurrentRange() {
		return checkRanges.peek().toString();
	}

	/**
	 * @return
	 */
	public String getSatRanges() {
		return satRanges.toString();
	}

	/**
	 * @return
	 */
	public String getTimeoutRanges() {
		return timeoutRanges.toString();
	}
	
	/**
	 * @return
	 */
	public String getUnsatRanges() {
		return unsatRanges.toString();
	}
	
	
	
	/**
	 * Resetting tag with parsing and initializing the range parameters.
	 */
	private void switchTag(String type) {
		currentTag = TAG_PREFIX + type;
		currentTagIndex = formulae.indexOf(currentTag);
		if (currentTagIndex == -1) throw new NoSuchElementException();
		
		checkFormulae = formulae.replaceFirst(currentTag, "");	// ready to check, needing no restoreFormulae()
		argLastIndex = formulae.indexOf("))\r\n", currentTagIndex);
		rangePredTokens = formulae.substring(currentTagIndex + currentTag.length(), argLastIndex).split("\\s+");

		// Preserving heading and tailing formulae for efficiency once the tag is not going to change
		prePredFormulae = formulae.substring(0, currentTagIndex);
		argRestFormulae = formulae.substring(argLastIndex, formulae.length());
	}

	private void switchTag(Type type) {
		switch (type) {
		case In: switchTag("In"); break;
		case UB: switchTag("UB"); break;
		case LB: switchTag("LB"); break;
		}
	}

	public void carryInTopDigit() {
		Parameters cilbound = checkRanges.peek().getLowerBound(), ciubound = new Parameters(cilbound.values);
		for (int i = 1; i < cilbound.dim; i++) ciubound.values[i] = cilbound.values[i] = ParamMin[i];
		do {
			cilbound.values[0]++; ciubound.values[0]+=2;
			CheckRange ciRange = new CheckRange(Type.In, cilbound, ciubound);
			if (!unsatRanges.contains(ciRange)) {checkRanges.push(ciRange); break;}
		} while (true);
	}

	/**
	 * Range degrading replacement types: (assuming non-negative integers)
	 * 	LB -> (timeout/unknown)LB*10 -> (timeout/unknown)MAX -> 
	 * 	(SAT/UNSAT)UB -> (timeout/unknown)UB/10 -> (timeout/unknown)-UB*10 -> (timeout/unknown)MIN -> 
	 * 	(SAT/UNSAT)IN -> (SAT/UNSAT)IN*10, 
	 * 					(timeout/unknown)IN/|10/degree| -> (SAT/UNSAT)IN+|10/degree|/param, where TODO
	 * 
	 * TODO Should be an instance method of {@link Degrader}!
	 * 
	 * @return
	 * @throws IOException 
	 */
	public String nextCheck() throws IOException {
		CheckRange currentRange = checkRanges.pop();
		
		Type currentType = currentRange.type;
		// Replacing the range predicate or switching predicate tagging 
		//	if not the first time checking (using no default parameters)
		Parameters nextBound; int i, paramIndex; 
		if (lastType != null) {
			if (currentType != lastType) switchTag(currentType);	// the first time switching is done by CheckRange(type)
			
			paramIndex = rangePredTokens.length - 1;
			switch (currentType) {
			case In: 
			case UB: 
				nextBound = currentRange.getUpperBound();
				for (i = noParams - 1; i >= 0; i--, paramIndex--)
					rangePredTokens[paramIndex] = String.valueOf(nextBound.values[i]);
				if (currentType == Type.UB) break;
			case LB: 
				nextBound = currentRange.getLowerBound();
				for (i = noParams - 1; i >= 0; i--, paramIndex--)
					rangePredTokens[paramIndex] = String.valueOf(nextBound.values[i]);
				// if (this.type == Type.LB) break;
			}
			
			checkFormulae = prePredFormulae;
			for (String t : rangePredTokens) checkFormulae += (t + " ");
			// trimming tailing space
			checkFormulae = checkFormulae.substring(0, checkFormulae.length()-1) + argRestFormulae;
		}
		
		
		// For preparing automated subsequent degrading checking
		String checkResult = currentRange.check();
		Parameters upperBound, lowerBound;
		// SAT: 
		if (checkResult.startsWith("sat")) {
			// Parsing model
			long[] satModel = new long[noParams];
			for (i = 0; i < noParams; i++) {
				paramIndex = checkResult.indexOf("(define-fun " + paramNames[i]) + "(define-fun ".length();
				satModel[i] = Long.valueOf(
						checkResult.substring(paramIndex, checkResult.indexOf(")\r\n", paramIndex)).split("\\s+")[3]);
			}
			nextBound = new Parameters(satModel);
			satRanges.add(new CheckRange(Type.In, nextBound));
			
			// for further split half's checking:
			switch (currentType) {
			case UB:
				// the lower half RangeUB one then the upper RangeIn one 
				checkRanges.push(new CheckRange(Type.In, nextBound.add(1), currentRange.getUpperBound()));
				checkRanges.push(new CheckRange(Type.UB, nextBound.add(-1)));
				break;
			case LB: 
				// the lower RangeIn one then upper half RangeLB one 
			case In: 
				final boolean isNotAPoint = !currentRange.isAPoint();
				if (currentType == Type.LB)	checkRanges.push(new CheckRange(Type.LB, nextBound.add(1)));
				else {	// if Type.In: the lower RangeIn one then upper half RangeIn one
					degradeInDegree--;
					upperBound = currentRange.getUpperBound();
					if (isNotAPoint && !nextBound.equals(upperBound)) checkRanges.push(new CheckRange(Type.In, nextBound.add(1), upperBound));
				}
				lowerBound = currentRange.getLowerBound();
				if (isNotAPoint && !nextBound.equals(lowerBound)) checkRanges.push(new CheckRange(Type.In, lowerBound, nextBound.add(-1)));
				break;
			}
		}
		
		// UNSAT:
		if (checkResult.startsWith("unsat")) {
			unsatRanges.add(currentRange);
			switch (currentType) {
			case LB: 
				// Changing to RangeUB checking with (lowerBound-1) as upperBound:
				//	Switching type b/w LB/UB needs no range parameter initialization
				checkRanges.push(new CheckRange(Type.UB, currentRange.getLowerBound().add(-1)));
				break;
			case UB:
				// Changing to RangeIn checking with (upperBound+1) as lowerBound:
				//	Switching type b/w UB/In needs range parameter initialization for storage 
				//	but not default value evaluation
			case In: 
				// No more ranges created for divide-and-conquer RangeIn checking
				degradeInDegree = 0;
				if (currentType == Type.In) {
//					degradeInDegree--;
					if (!checkRanges.isEmpty()) break;
				}
				// Or to the next expanding-digit and carry-in range for the top level RangeIn checking
				nextBound = currentRange.getUpperBound();
				if (currentType == Type.UB) {
					upperBound = nextBound.multi(10);
				} else {	// if Type.In: 
					upperBound = nextBound.add((int)Math.pow(10, Math.abs(degradeInDegree)), noDegradeInParam);
					if (noDegradeInParam < noParams) noDegradeInParam++;
				}
				checkRanges.push(new CheckRange(Type.In, nextBound.add(1), upperBound));
			}
		}
		
		// timeout/unknown: Restoring the old degrading tag comment and advancing to the next one
		if (checkResult.startsWith("timeout") || checkResult.startsWith("unknown")) 
			switch (currentType) {
			case LB: 
				// To the next digit-expanded lower bound (TODO: till MAX, Z3 function evaluation needed)
				checkRanges.push(new CheckRange(Type.LB, currentRange.getLowerBound().multi(10)));
				break;
			case UB: 
				// To the next digit-shrunk upper bound (TODO: till MIN, Z3 function evaluation needed)
				checkRanges.push(new CheckRange(Type.UB, currentRange.getUpperBound().divide(10)));
				break;
			case In: 
				// Retreating to the origin (lower bound) 
//				nextBound = currentRange.getLowerBound();
//				nextBound2 = Arrays.copyOf(nextBound, noParam);	// Backing up the lower bound
				// and to next shrinking-digit and carry-out range till 1+
//				degradeInDegree += (degradeInDegree == -1)?3:1;
//				nextRange = Math.max(1, 10/Math.abs(degradeInDegree));
//				for (i = noParam - noDegradeInParam; i < noDegradeInParam; i++) nextBound2[i] = nextBound[i] + nextRange;
//				if (nextRange == 1 && noDegradeInParam > 1) noDegradeInParam--;
//				checkRanges.push(new CheckRange(Type.In, nextBound, nextBound2));
//				break;
				
				// To the upper (shorter) divide-and-conquer half then the lower (longer) one for expMean and stack's nature
				degradeInDegree++;
				upperBound = currentRange.getUpperBound();
				lowerBound = currentRange.getLowerBound();

				if (currentRange.isAPoint()) {
					timeoutRanges.add(currentRange);
					return "!!!" + checkResult.substring(0, 7) + ": should apply quantifier degrading!!!\r";
				}
				
				do {
					nextBound = upperBound.expMean(lowerBound, degradeInDegree);// up-side down exponential mean computing
					if (nextBound.equals(lowerBound)) {
						if (nextBound.equals(upperBound)) break;	// if upperBound == lowerBound
						else nextBound = upperBound;				// if upperBound == lowerBound + 1
					}
					checkRanges.push(new CheckRange(Type.In, nextBound, upperBound));
					upperBound = nextBound.add(-1);
				} while (!nextBound.equals(lowerBound));
				checkRanges.push(new CheckRange(Type.In, lowerBound, upperBound));
				break;
			}
		
		lastType = currentType;
		
		return checkResult;
	}

	@Override
	protected CheckRange nextDegrading() throws NoSuchElementException {
		return null;
	}
	
	
	
	@Override
	public void resetCheck() {
	}

	/**
	 * TODO Should be an instance method of {@link Degrader}!
	 */
	protected void restoreFormulae() {
		checkFormulae = formulae;
	}
	
	@SuppressWarnings("removal")
    static public String toZ3SmtDeclaration(Parameter... params) {
		if (params.length <= 1) {
			final Parameter p = params == null || params.length == 0 
					? (defaultParam == null ? DebugElement.throwInvalidityException("no parameters") : defaultParam)
					: params[0];
			final String pname = p.getPeer1(), 
					ptype = p.getPeer2().toZ3SmtString(true, true),
					MIN = p.min, MAX = p.max;
			return 
				";_LB,     _1,    _UB\r\n" + 
				"(define-fun InCarryInRange ((_1 " + ptype + ")(_LB " + ptype + ")(_UB "+ ptype + ")) Bool (and\r\n" + 
				"  (<= _LB _1)(<= _1 _UB)\r\n" + 
				"))\r\n" + 
				"(define-fun InCarryInRangeUB ((_1 " + ptype + ")(_UB " + ptype + ")) Bool (or\r\n" + 
				"  (= _1 _UB)\r\n" + 
				"  (< _1 _UB)\r\n" + 
				"))\r\n" + 
				"(define-fun InCarryInRangeLB ((_1 " + ptype + ")(_LB " + ptype + ")) Bool (or\r\n" + 
				"  (= _1 _LB)\r\n" + 
				"  (> _1 _LB)\r\n" + 
				"))\r\n\r\n" + 
				"(echo \"Range down-grade...\")\r\n" + 
				";RangeDegradeUB(define-fun InRange ((_1 " + ptype + ")) Bool (InCarryInRangeUB _1 " + MAX + "))\r\n" + 
				";RangeDegradeIn(define-fun InRange ((_1 " + ptype + ")) Bool (InCarryInRange _1 " + MIN + " " + MAX +"))\r\n" + 
				";RangeDegradeLB(define-fun InRange ((_1 " + ptype + ")) Bool (InCarryInRangeLB _1 " + MIN + "))\r\n" + 
				";RangeDegradeParams(assert (InRange " + pname + "))\r\n";
		}
		
		return DebugElement.throwTodoException("multi-parameter");
//		return ";(_LB1,     (_1,    (_LB1,         (_1,      (_LB1 + 1,      (_1,      (_UB1,    (_1,      (_UB1,    (_1,      (_UB1,\r\n" + 
//				";_LB2,   ... _2, ... _LB2 + 1,  ... _2,   ... MIN,        ... _2,   ... MIN,   ..._2,   ... _UB2, ... _2,   ... _UB2,\r\n" + 
//				";_LB3)       _3)     MIN)           _3)       MIN)            _3)       MIN)      _3        MIN)      _3        _UB3)\r\n" + 
//				"(define-fun InCarryInRange ((_1 Int)(_2 Int)(_3 Int)(_LB1 Int)(_LB2 Int)(_LB3 Int)(_UB1 Int)(_UB2 Int)(_UB3 Int)) Bool (and\r\n" + 
//				"  (<= _LB1 _1)(<= _1 _UB1)\r\n" + 
//				"  (ite (= _LB1 _UB1) \r\n" + 
//				"    (ite (= _LB2 _UB2) (and (= _LB2 _2)(<= _LB3 _3)(<= _3 _UB3)) \r\n" + 
//				"      (or (and (= _LB2 _2)(<= _LB3 _3))\r\n" + 
//				"        (and (< _LB2 _2)(< _2 _UB2))\r\n" + 
//				"        (and (= _2 _UB2)(<= _3 _UB3))))\r\n" + 
//				"    (or (and (= _LB1 _1)(= _LB2 _2)(<= _LB3 _3))\r\n" + 
//				"      (and (= _LB1 _1)(< _LB2 _2)) \r\n" + 
//				"      (and (< _LB1 _1)(< _1 _UB1))\r\n" + 
//				"      (and (= _1 _UB1)(< _2 _UB2))\r\n" + 
//				"      (and (= _1 _UB1)(= _2 _UB2)(<= _3 _UB3))))\r\n" + 
//				"))\r\n" + 
//				"(define-fun InCarryInRangeUB ((_1 Int)(_2 Int)(_3 Int)(_UB1 Int)(_UB2 Int)(_UB3 Int)) Bool (or\r\n" + 
//				"  (and (= _1 _UB1) (or (and (= _2 _UB2)(<= _3 _UB3)) (< _2 _UB2)))\r\n" + 
//				"  (< _1 _UB1)\r\n" + 
//				"))\r\n" + 
//				"(define-fun InCarryInRangeLB ((_1 Int)(_2 Int)(_3 Int)(_LB1 Int)(_LB2 Int)(_LB3 Int)) Bool (or\r\n" + 
//				"  (and (= _1 _LB1) (or (and (= _2 _LB2)(>= _3 _LB3)) (> _2 _LB2)))\r\n" + 
//				"  (> _1 _LB1)\r\n" + 
//				"))\r\n" + 
//				"\r\n" + 
//				";(assert (Inv t1 t2 i1 i2 chunk_size nthreads x ist iend lu_fp nx0 ny0 nz0 nx ny nz jst jend j1 j2 m1)) ;Inv should be obeyed all the time\r\n" + 
//				"\r\n" + 
//				"(echo \"Range down-grade...\")\r\n" + 
//				";RangeDegradeUB(define-fun InCarryInRange ((_1 Int)(_2 Int)(_3 Int)) Bool (InCarryInRangeUB _1 _2 _3 100 100 100))\r\n" + 
//				";RangeDegradeIn(define-fun InCarryInRange ((_1 Int)(_2 Int)(_3 Int)) Bool (InCarryInRange _1 _2 _3 1 3 0 1 3 0))\r\n" + 
//				";RangeDegradeLB(define-fun InCarryInRange ((_1 Int)(_2 Int)(_3 Int)) Bool (InCarryInRangeLB _1 _2 _3 2147483647 2147483647 2147483647))\r\n" + 
//				";(define-fun InCarryInRange ((_1 Int)(_2 Int)(_3 Int)) Bool (InCarryInRange _1 _2 _3 1 2 (+ 7 1) 4611686018427387902 2 4611686018427387905))\r\n" + 
//				";(define-fun InCarryInRange ((_1 Int)(_2 Int)(_3 Int)) Bool (InCarryInRangeUB _1 _2 _3 1 2 (- 5 1)))\r\n" + 
//				";(define-fun InCarryInRange ((_1 Int)(_2 Int)(_3 Int)) Bool (InCarryInRangeLB _1 _2 _3 4611686018427387902 2 (+ 4611686018427387905 1)))\r\n" + 
//				";(define-fun InCarryInRange ((_1 Int)(_2 Int)(_3 Int)) Bool (InCarryInRange _1 _2 _3 1 0 1 1 (div MAX 100000000000000) (div MAX 100000000000000)))\r\n" + 
//				";RangeDegradeParams(assert (InCarryInRange chunk_size nthreads x))\r\n";
	}
	
}