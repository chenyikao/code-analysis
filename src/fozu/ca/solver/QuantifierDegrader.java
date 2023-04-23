package fozu.ca.solver;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Stack;
import java.util.function.BiConsumer;

/**
 * 
 */

/**
 * Degrading procedure:
 * 	1.	Shifting and reduction current forall quantifiers;
 * 	(Degrading formulae:)
 * 	2.	Traversing all quantifier declaration positions and re-arranging the shifted and reduced declaration;
 * 	3.	Toggling non-declaration exist/forall formulae.
 *  
 * @author Kao, Chen-yi
 *
 */
public class QuantifierDegrader extends DegraderChecker<QuantifierDegrader.ForallQuantifiers> {
	
	private static final String TAG_PREFIX = ";QuantDegrade";
	private static final String TAG_EXIST_INFIX = "Exist";
	private static final String TAG_FORALL_INFIX = "Forall";
	private static final String TAG_DECL_SUFFIX = "Decl";
	private static final String TAG_GLOBAL_SUFFIX = "Global";
	
	protected static final NoSuchElementException NOT_YET_ITERATE_EXCEPTION = new NoSuchElementException();
	protected static final NoSuchElementException END_OF_SHIFT_EXCEPTION = NOT_YET_ITERATE_EXCEPTION;
	protected static final NoSuchElementException END_OF_REDUCE_EXCEPTION = END_OF_SHIFT_EXCEPTION;

	
	
	protected static class ForallQuantifiers extends Degrading implements Cloneable, Iterable<Integer> {

		static protected final List<String> GLOBAL_NAMES = new ArrayList<String>();
		static private int ALL_QUANTIFIERS_SIZE;					// supposed write-once/final
		
		final private List<Integer> quantifiers = new ArrayList<Integer>();
		private QuantifierDegrader formulaChecker;					// supposed write-once/final

		private int reduceSize = 0;
		final private Stack<Integer> shiftStack = new Stack<Integer>();

		
		
		/**
		 * 
		 */
		public ForallQuantifiers(QuantifierDegrader checker) {
			formulaChecker = checker;
		}

		public ForallQuantifiers(QuantifierDegrader checker, List<Integer> qlist) {
			this(checker);
			quantifiers.addAll(qlist);
		}

		public ForallQuantifiers(QuantifierDegrader checker, int prefilledSize) {
			this(checker);
			for (int i = 1; i <= prefilledSize; i++) quantifiers.add(i);
		}
		


		protected void shift() throws NoSuchElementException {
			// Shifting with carry-in
			int shiftIdx, carryIn = -1, carryInUB = ALL_QUANTIFIERS_SIZE, i;
			do {
				if (shiftStack.isEmpty()) throw END_OF_SHIFT_EXCEPTION;	// If no shifting available...
				carryIn++;
				shiftIdx = shiftStack.pop();
			} while (shiftIdx == carryInUB--);
			
			shiftStack.push(shiftIdx + 1);
			for (i = 1; i <= carryIn; i++) shiftStack.push(shiftIdx + 1 + i);

			// Go shifting to the indicated quantifier combination
			quantifiers.clear();
			Iterator<Integer> shiftIdxs = shiftStack.iterator();
			assert(shiftIdxs.hasNext());
			shiftIdx = shiftIdxs.next();
			for (i = 1; i <= ALL_QUANTIFIERS_SIZE; i++) {
				if (i != shiftIdx) quantifiers.add(i);
				if (i == shiftIdx && shiftIdxs.hasNext()) shiftIdx = shiftIdxs.next();
			}
		}

		protected void reduce() throws NoSuchElementException {
			// If no reduction available...
			if (reduceSize == ALL_QUANTIFIERS_SIZE) throw END_OF_REDUCE_EXCEPTION;
			
			// Go reducing to the indicated quantifier combination
			reduceSize++;
			int i = 1;
			for (; i <= reduceSize; i++) shiftStack.push(i);

			quantifiers.clear();
			for (; i <= ALL_QUANTIFIERS_SIZE; i++) quantifiers.add(i);
		}

		/**
		 * Two types of quantifier declaring formula to degrade:
		 * 	1.	... (qn Int) ...
		 * 	2.	( ... qn ... )
		 * 
		 * @see Degrading#degradeFormulae()
		 */
		@Override
		protected String degradeFormulae() {
			// original backup formulae -> current one
//			formulaChecker.restoreFormulae();
			
			// 	2.	Traversing all quantifier declaration positions and re-arranging the shifted and reduced declaration;
			// 	3.	Toggling non-declaration exist/forall formulae.
			return formulaChecker.toggleFormulae();
		}
		
		
		
		/**
		 * @see java.lang.Object#clone()
		 */
		@Override
		public Object clone() {
			return new ForallQuantifiers(formulaChecker, quantifiers);
		}

		/* (non-Javadoc)
		 * @see java.lang.Object#equals(java.lang.Object)
		 */
//		@Override
//		public boolean equals(Object obj) {
//			return (obj instanceof Quantifiers) && super.equals(obj);
//		}

		/**
		 * TODO: 
		 * 	1.	checking for quantifier size inconsistency
		 * 	2.	providing canonical quantifier name declaration
		 * 
		 * @param qIndex - an 1-base index number
		 * @param qName
		 */
//		public void add(int qIndex, String qName) {
//			quantifiers.add(qIndex-1, (qName.startsWith("_"))?qName.substring(1):qName);
//		}
		
		/**
		 * @param qIndex - an 1-base index number
		 * @return
		 */
		public Integer get(int qIndex) {
			return quantifiers.get(qIndex-1);
		}
		
		public Integer last() {
			return quantifiers.get(ALL_QUANTIFIERS_SIZE-1);
		}
		
		@Override
		public Iterator<Integer> iterator() {
			return quantifiers.iterator();
		}
		
		public String toString() {
			String str = "forall ";
			for (int qIdx : quantifiers) str += (GLOBAL_NAMES.get(qIdx - 1) + ",");
			return str;
		}

		public int size() {
			return quantifiers.size();
		}

		public boolean isEmpty() {
			return quantifiers.isEmpty();
		}

	}

	
	
	
	
	/**
	 * Null means the initial and not-yet-iterated state;
	 * while an empty list means ALL quantifiers existential.
	 */
	private ForallQuantifiers currentQuantifiers = null;
	
	final private List<String> declFreeFormulae = new ArrayList<String>();
//	final private ArrayList<String> originalDFFBackup = new ArrayList<String>();
	
	/**
	 * Mapping declFreeFormulae indexes to tag lines for more efficient formula backup and restoring.
	 * 
	 * List<String>.get(0) == tag-commented line
	 * List<String>.get(1) == uncommented formula
	 * List<String>.get(2), ... all local quantifier names
	 */
	final private Map<Integer, List<String>> existDeclMap = new HashMap<Integer, List<String>>();
	final private Map<Integer, List<String>> forallDeclMap = new HashMap<Integer, List<String>>();
	final private Map<Integer, List<String>> existMap = new HashMap<Integer, List<String>>();
	final private Map<Integer, List<String>> forallMap = new HashMap<Integer, List<String>>();

	
	
	/**
	 * Parsing formulae to build all quantifiers, storing tag positions and check tags.
	 * 
	 * Quantifier-to-degrade tag (four types of tags):
	 * 	";" ("QuantDegradeExist"|"QuantDegradeForall") "Decl" 	";" q1 ";" q2 ";" ... ";" qn ";" formulae
	 * 	";" ("QuantDegradeExist"|"QuantDegradeForall") 			";" q1 ("->" q1p)? ";" q2 ("->" q2p)? ";" ... ";" qn ("->" qnp)? ";" formulae
	 * 
	 * @param formulae
	 */
	public QuantifierDegrader(String formulae) {
		declFreeFormulae.add(formulae);
		
		int tagIdx, upfIdx, tagLineIdx, tagLineEndIdx, formulaIdx; 
		String unparsedFormulae, tagLine, tag, tagToken[], qToken[];
		List<String> tagLineList;
		do {
			// starting from the last (unparsed) part of formulae
			upfIdx = declFreeFormulae.size() - 1;
			unparsedFormulae = declFreeFormulae.get(upfIdx);
			tagIdx = unparsedFormulae.indexOf(TAG_PREFIX);
			if (tagIdx == -1) continue;

			tagLineEndIdx = unparsedFormulae.indexOf(System.getProperty("line.separator"), tagIdx);
			tagLine = unparsedFormulae.substring(tagIdx, tagLineEndIdx);
			formulaIdx = tagLine.indexOf("(");
			if (formulaIdx == -1) {	
				formulaIdx = tagLine.indexOf(")");
				if (formulaIdx == -1) {	// skipping the parsed pure comment part and rearranging formulae storage
					declFreeFormulae.set(upfIdx, unparsedFormulae.substring(0, tagIdx));
					declFreeFormulae.add(unparsedFormulae.substring(tagLineEndIdx));
					continue;
				}
			}

			tag = tagLine.substring(0, formulaIdx);
			tagToken = tag.split(";");	// tagToken[0] == ""
			qToken = Arrays.copyOfRange(tagToken, 2, tagToken.length);
			tagLineList = new ArrayList<String>(Arrays.asList(new String[] {tagLine}));
			// ready to examine quantifier and check for quantifier declaration formulae without any comment
			tagLineList.add(tagLine.substring(formulaIdx).split(";")[0]);
			tagLineList.addAll(Arrays.asList(qToken));
			
			// parsing tag: storing tag position -> (extracting variables -> removing tag)
			tagLineIdx = upfIdx + 1;
			switch (tagToken[1].substring(TAG_PREFIX.length() - 1)) {
			case TAG_EXIST_INFIX:
				existMap.put(tagLineIdx, setQTrans(tagLineList)); break;
			case TAG_FORALL_INFIX:
				forallMap.put(tagLineIdx, setQTrans(tagLineList)); break;
				
				// parsing exist/forall quantifier declaration: extracting variables -> removing tag
			case TAG_EXIST_INFIX + TAG_DECL_SUFFIX + TAG_GLOBAL_SUFFIX:
				setGlobalNames(qToken);
			case TAG_EXIST_INFIX + TAG_DECL_SUFFIX:
				existDeclMap.put(tagLineIdx, tagLineList); break;
			case TAG_FORALL_INFIX + TAG_DECL_SUFFIX + TAG_GLOBAL_SUFFIX:
				setGlobalNames(qToken);
			case TAG_FORALL_INFIX + TAG_DECL_SUFFIX:
				forallDeclMap.put(tagLineIdx, tagLineList);
			}
			
			// rearranging formulae storage to store the parsed part
			declFreeFormulae.set(upfIdx, unparsedFormulae.substring(0, tagIdx));
			declFreeFormulae.add(tagLine);
			declFreeFormulae.add(unparsedFormulae.substring(tagLineEndIdx));
			
		} while (tagIdx != -1);
		
		// current formulae -> original backup one
//		backupFormulae();
	}
	


	/**
	 * Taking only tagToken[2] ~ tagToken[length-1] since tagToken[0]="" and tagToken[1] is the title of tag.
	 * 
	 * @param qToken
	 */
	private void setGlobalNames(String[] qToken) {
		for (String q : qToken) if (!ForallQuantifiers.GLOBAL_NAMES.contains(q)) ForallQuantifiers.GLOBAL_NAMES.add(q);
		ForallQuantifiers.ALL_QUANTIFIERS_SIZE = ForallQuantifiers.GLOBAL_NAMES.size();
	}

	private List<String> setQTrans(List<String> oldList) {
		String qs[];
		for (int i = 2; i < 2 + ForallQuantifiers.ALL_QUANTIFIERS_SIZE; i++) {
			qs = oldList.get(i).split("->");
			oldList.set(i, qs[0]);
			oldList.add(qs[1]);
		}
		return oldList;
	}
	


	public String getCurrentQuantifiers() throws NoSuchElementException {
		return getCurrentDegradingString();
	}
	
	public ForallQuantifiers getCurrentDegrading() throws NoSuchElementException {
		if (currentQuantifiers == null) throw NOT_YET_ITERATE_EXCEPTION;
		return currentQuantifiers;
	}
	
	/**
	 * Degrading procedure -
	 * 	1.	Shifting and reduction current forall quantifiers
	 * 
	 * Quantifier degrading policy:
	 * 	1.	All (n) forall -> ni forall -> none forall
	 * 	2.	Quantifier shifting and reduction: q1 -> qni
	 * 	ex.		q1,q2,q3,q4,q5,q6	(shift: '',		reduce: 0)
	 * 		->	q2,q3,q4,q5,q6		(shift: 'q1',	reduce: 1)
	 * 		->	q1,q3,q4,q5,q6		(shift: 'q2',	reduce: 1)
	 * 		->	q1,q2,q4,q5,q6		(shift: 'q3',	reduce: 1)
	 * 		->	q1,q2,q3,q5,q6		(shift: 'q4',	reduce: 1)
	 * 		->	q1,q2,q3,q4,q6		(shift: 'q5',	reduce: 1)
	 * 		->	q1,q2,q3,q4,q5		(shift: 'q6',	reduce: 1)
	 * 		->	q3,q4,q5,q6			(shift: 'q1,q2',	reduce: 1)
	 * 		->	q2,q4,q5,q6			(shift: 'q1,q3',	reduce: 1)
	 * 		->	...
	 * 
	 * @see DegraderCheck#nextDegrading()
	 */
	@Override
	public ForallQuantifiers nextDegrading() throws NoSuchElementException {
		if (currentQuantifiers != null) 
			// Advancing to the next of the next Quantifiers
			try {
				currentQuantifiers.shift();
			} catch(NoSuchElementException e) {
				currentQuantifiers.reduce();
			}

		else currentQuantifiers = new ForallQuantifiers(this, ForallQuantifiers.ALL_QUANTIFIERS_SIZE);
		
		return currentQuantifiers;
	}

	/**
	 * @param forallQ - null or an array of empty string(s) means ALL quantifiers existential
	 * @return
	 * @throws NoSuchElementException
	 * @throws IOException
	 */
	public String nextCheck(String[] forallQ) throws NoSuchElementException, IOException {
		List<Integer> qList = new ArrayList<Integer>();
		
		for (int i = 1; i <= ForallQuantifiers.ALL_QUANTIFIERS_SIZE; i++)
			for (String name : forallQ) if (name.equals(ForallQuantifiers.GLOBAL_NAMES.get(i-1))) qList.add(i);
		
		currentQuantifiers = new ForallQuantifiers(this, qList);
		return currentQuantifiers.check();
	}



	public void resetCheck() {
		currentQuantifiers = null;
	}
	
	
	
	public String getFormulae() {
		String formulae = "";
		for (String partFormulae : declFreeFormulae) formulae += partFormulae;
		return formulae;
	}



//	private void backupFormulae() {
//		assert originalDFFBackup.isEmpty();
//		for (String partFormulae : declFreeFormulae) originalDFFBackup.add(new String(partFormulae));
//	}
	
	
	
	public void restoreFormulae() {
//		declFreeFormulae.clear();
//		for (String partFormulae : originalDFFBackup) declFreeFormulae.add(new String(partFormulae));
		// tag maps as backup
		existDeclMap.forEach(restoreTagLine());
		forallDeclMap.forEach(restoreTagLine());
		existMap.forEach(restoreTagLine());
		forallMap.forEach(restoreTagLine());
	}
	/**
	 * @return
	 */
	private BiConsumer<? super Integer, ? super List<String>> restoreTagLine() {
		return (k, v) -> declFreeFormulae.set(k, v.get(0));
	}
	
	
	
	/**
	 * @return
	 */
	public String toggleFormulae() {
		if (currentQuantifiers != null) {
			
			List<Integer> existQs = new ArrayList<Integer>();
			Iterator<Integer> forallQs = currentQuantifiers.iterator();
			for (int i = 0, forallQ = 0; i <= ForallQuantifiers.ALL_QUANTIFIERS_SIZE; i++) {
				if (i != forallQ) existQs.add(i);
				else if (forallQs.hasNext()) forallQ = forallQs.next();	// including the initial case of 0 == 0
			}
			
			// 	2.	Traversing all quantifier declaration positions and re-arranging the shifted and reduced declaration;
			// Forall quantifier declaration formula degrading replacement: 
			//	removing exist quantifier declarations;
			//	ALL forall quantifiers removal means a function-less forall declaration, which equals one that remaining commented.
			if (existQs.size() < ForallQuantifiers.ALL_QUANTIFIERS_SIZE) forallDeclMap.forEach((k, v) -> removeDeclQ(k, v, existQs));
			else forallDeclMap.forEach(restoreTagLine());						// the code line is NOT ALWAYS shown (uncommented) to solver
			// Exist quantifier declaration formula upgrading replacement: complement to the forall's
			existDeclMap.forEach((k, v) -> removeDeclQ(k, v, currentQuantifiers));
			
			// 	3.	Toggling non-declaration exist/forall formulae.
			// Forall quantifier formula degrading replacement: transitioning quantifiers with forall quantifier references
			forallMap.forEach((k, v) -> transLineQ(k, v, currentQuantifiers));	// the code line is ALWAYS shown (uncommented) to solver
			// Exist quantifier formula upgrading replacement: transitioning quantifiers with exist quantifier references
			existMap.forEach((k, v) -> transLineQ(k, v, existQs));
			
		}
		return getFormulae();
	}
	/**
	 * @param formulaIdx
	 * @param decl
	 * @param qsToRemove - quantifiers to remove
	 */
	private void removeDeclQ(int formulaIdx, List<String> decl, Iterable<Integer> qsToRemove) {
		String qRemovedDecl = decl.get(1), qLocal;
		for (int q : qsToRemove) {
			qLocal = decl.get(q + 1);
			qRemovedDecl = qRemovedDecl.replaceFirst("(" + qLocal + "\\s)|(\\(" + qLocal + "\\sInt\\))", "");
		}
		declFreeFormulae.set(formulaIdx, qRemovedDecl);
	}
	/**
	 * @param formulaIdx
	 * @param line
	 * @param qsToRef - quantifiers to reference
	 */
	private void transLineQ(int formulaIdx, List<String> line, Iterable<Integer> qsToRef) {
		String formula = line.get(1);
		for (int q : qsToRef) 
			formula = formula.replaceAll("\\b" + line.get(q + 1) + "\\b", line.get(q + 1 + ForallQuantifiers.ALL_QUANTIFIERS_SIZE));
		declFreeFormulae.set(formulaIdx, formula);
		return;
	}

}
