/**
 * 
 */
package fozu.ca.vodcg.condition;

import java.lang.reflect.Method;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

import org.eclipse.jdt.core.dom.Name;

import fozu.ca.Elemental;
import fozu.ca.condition.SerialFormat;
import fozu.ca.vodcg.IncomparableException;
import fozu.ca.vodcg.ReenterException;
import fozu.ca.vodcg.SystemElement;
import fozu.ca.vodcg.UncertainPlaceholderException;
import fozu.ca.vodcg.VODCondGen;
import fozu.ca.vodcg.condition.data.ArithmeticGuard;
import fozu.ca.vodcg.condition.data.PlatformType;

/**
 * @author Kao, Chen-yi
 *
 * @param <S>
 */
public abstract class Reference<S extends Referenceable> 
extends Referenceable {

	public static final String ILLEGAL_SUBJECT_EXCEPTION = "Must provide a non-null subject to reference!";

	private static final Method METHOD_DEPENDS_ON = 
			Elemental.getMethod(Reference.class, "dependsOn", Expression.class);
	private static final Method METHOD_GET_SUBJECT = 
			Elemental.getMethod(Reference.class, "getSubject");

	
	
	private S subject;
	/**
	 * for delayed subject observation
	 */
	private Function<Reference<S>, S> subjectSup = null;

	
	
	@SuppressWarnings("removal")
	protected Reference(String name, Function<Reference<S>, S> sbjSup, boolean isInAST, Boolean isGlobal, VODCondGen condGen) {
		super(name, (S) null, condGen);
		
		if (sbjSup == null) throwTodoException(ILLEGAL_SUBJECT_EXCEPTION);
		subjectSup = sbjSup;
		
		init(isInAST, isGlobal);
	}
	
	protected Reference(S subject, boolean isInAST, Boolean isGlobal) {
		super(subject, getNonNull(subject::getScopeManager));
		
		assert subject != null;
//		initSubject(subject);
		setSubject(subject);

		init(isInAST, isGlobal);
	}
	
	private void init(boolean isInAST, Boolean isGlobal) {
		if (!isInAST) {
			setNonAST();
			setConstant(false);	// default not-constant for non-AST references
		}
		setGlobal(isGlobal);
	}


	
	@Override
	public String getName() {
		return get(
				super::getName, e -> getSubject().getName());
	}
	
//	/**
//	 * @return C name in {@link IName} form.
//	 */
//	@Override
//	public IName getIName() {
//		return get(
//				()-> super.getIName(), e-> getSubject().getIName());
//	}
	
	/**
	 * @return C name in {@link IASTName} form.
	 */
	@SuppressWarnings("removal")
	@Override
	public Name getASTName() {
		return debugGet(()-> peekASTName(), 
				e-> getSubject().getASTName());
	}


	
	@Override
	protected ConditionElement cacheScope() {
		// lazy scope setting while subject's scope (expression or function) is ready
		return subject.getScope();
	}
	
	/**
	 * @return
	 */
	public ConditionElement getNonReferenceScope() {
		return super.getScope();
	}
	


	@Override
	public PlatformType getType() {
		final PlatformType t = get(this::getReferenceableType,
				()-> getSubject().getType());
		setType(t);
		return t;
	}
	
	protected PlatformType getReferenceableType() {
		return super.getType();
	}

	/**
	 * @return a non-null set
	 */
	@Override
	protected <T> Set<T> cacheDirectVariableReferences(Class<T> refType) {
		final Set<T> vrs = new HashSet<>();
		final S sbj = getSubject();
		if (sbj != null) {
			Set<T> sbjVrs = sbj.cacheDirectVariableReferences(refType);
			if (sbjVrs != null) vrs.addAll(sbjVrs);
		}
		return vrs;
	}
	
	@Override
	protected Set<ArithmeticGuard> cacheArithmeticGuards() {
		return getSubject().getArithmeticGuards();
	}
	
	/**
	 * A reference SHOULD have in-direct references normally,
	 * as direct (subject-owned) ones by default.
	 * 
	 * @see fozu.ca.vodcg.condition.ConditionElement#cacheDirectFunctionReferences()
	 */
	@Override
	protected Set<fozu.ca.vodcg.condition.Function> cacheDirectFunctionReferences() {
		return getSubject().getDirectFunctionReferences();
	}

	@Override
	protected void cacheDirectSideEffect() {
		andSideEffect(()-> getSubject().getSideEffect());
	}
	
	
	
	public final S peekSubject() {
		return subject;
	}
	
	/**
	 * @return the subject
	 */
	public S getSubject() 
			throws ReenterException, IncomparableException, UncertainPlaceholderException {
		if (subject == null && subjectSup == null) throwNullArgumentException("subject");
		try {
			return subject == null 
					? guardThrow(()-> setSubject(subjectSup.apply(this)),
							METHOD_GET_SUBJECT) 
					: subject;
//		if (subject == null) setSubject(debugCallDepth(30, subjectSup));

		} catch (ReenterException 
				| IncomparableException 
				| UncertainPlaceholderException e) {	
			// thrown by subjectSup.get() -> initVersion()
//			e.leave();
			throw e;
		} catch (Exception e) {
			return throwUnhandledException(e, METHOD_GET_SUBJECT);
		}
	}



//	private void initSubject(Subject newSubject) {
//		assert newSubject != null;
//		subject = newSubject;
//	}
	
	public S setSubject(S newSubject) {
		if (newSubject == null) throwNullArgumentException("subject");
//		initSubject(newSubject);
		subject = newSubject;
//		setName(newSubject.getName());
//		if (tests(newSubject.isGlobal())) setGlobal();
		return newSubject;
	}

	
	
	@Override
	public void setName(String newName) {
		final S sbj = peekSubject();
		if (sbj == null) {
			// during initialization
			if (newName != null) super.setName(newName);
		} else 
			sbj.setName(newName);
	}
	
	public final void setReferenceableName(String newName) {
		super.setName(newName);
	}
	
	
	
	@Override
	protected Boolean cacheConstant() {
		assert getSubject() != null;
		return getNonNull(this::getSubject).isConstant();
	}
	
	@SuppressWarnings("unchecked")
	@Override
	protected Expression toConstantIf() {
		return this;
	}

	
	
	@Override
	public boolean contains(Expression exp) {
		return equals(exp);
	}

	@Override
	protected boolean equalsToCache(SystemElement e2) {
		if (e2 == null) return false;
		
		Referenceable ref2Subject = ((Reference<?>) e2).subject;
		return ((subject == null) ? ref2Subject == null : subject.equals(ref2Subject))
				// {@link Reference} do concern location equality!
				&& super.equalsWithoutLocality(e2, false);
	}
	
	@Override
	protected List<Integer> hashCodeVars() {
		// {@link Reference} do concern location equality!
		List<Integer> hcvs = new ArrayList<>(hashCodeVarsWithLocality(false));
		hcvs.add(subject == null ? 0 : subject.hashCode()); 
		return hcvs;
	}
	
	/**
	 * @return Should be always false.
	 *fozu.ca fozu.ca.condition.Referenceable#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		return subject == null;
	}
	
	@Override
	public Boolean dependsOn(Expression e) {
		return testsAnySkipNull(
				()-> super.dependsOn(e),		// e == this
				()-> guardSkipException(()-> subject.dependsOn(e), METHOD_DEPENDS_ON)); 
	}
	
	
	
	/**
	 * Both ambiguous names and keyword-avoidance are already considered by 
	 * {@link Referenceable}.
	 * 
	 * TODO: a reference only has to consider ??
	 * 
	fozu.caee fozu.ca.condition.Referenceable#disambiguateZ3SmtString(java.lang.String, java.lang.String)
	 */
	@Override
	public String disambiguateZ3SmtString(String originalTerm, String disambiguousTerm) {
		return super.disambiguateZ3SmtString(
				VODCondGen.findSymbol(this, SerialFormat.Z3_SMT), disambiguousTerm); 
	}

}