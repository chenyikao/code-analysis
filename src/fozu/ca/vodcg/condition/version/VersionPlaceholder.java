package fozu.ca.vodcg.condition.version;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.NavigableSet;
import java.util.Set;
import java.util.function.Function;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.Statement;

import fozu.ca.Addressable;
import fozu.ca.condition.SerialFormat;
import fozu.ca.vodcg.ASTException;
import fozu.ca.vodcg.Assignable;
import fozu.ca.vodcg.IncomparableException;
import fozu.ca.vodcg.ReenterException;
import fozu.ca.vodcg.SystemElement;
import fozu.ca.vodcg.UncertainException;
import fozu.ca.vodcg.UncertainPlaceholderException;
import fozu.ca.vodcg.VODCondGen;
import fozu.ca.vodcg.condition.ArithmeticExpression;
import fozu.ca.vodcg.condition.AssignableExpression;
import fozu.ca.vodcg.condition.Expression;
import fozu.ca.vodcg.condition.ExpressionRange;
import fozu.ca.vodcg.condition.Proposition;
import fozu.ca.vodcg.condition.Reference;
import fozu.ca.vodcg.condition.Referenceable;
import fozu.ca.vodcg.condition.Variable;
import fozu.ca.vodcg.condition.data.DataType;
import fozu.ca.vodcg.condition.data.Int;
import fozu.ca.vodcg.condition.data.NumericExpression;
import fozu.ca.vodcg.condition.data.PlatformType;
import fozu.ca.vodcg.condition.data.Real;

/**
 * A {@link Version} placeholder/controller of model-view-controller-like pattern.
 *  
 * @author Kao, Chen-yi
 *
 */
public abstract class VersionPlaceholder<S extends Referenceable> 
extends Reference<Version<? extends S>> 
implements VersionEnumerable<S>, AssignableExpression {

//	static private final Method METHOD_IS_POSITIVE = 
//			Elemental.getMethod(VersionPlaceholder.class, "isPositive");
//	static private final Method METHOD_IS_POSITIVE_INFINITY = 
//			Elemental.getMethod(VersionPlaceholder.class, "isPositiveInfinity");
//	static private final Method METHOD_IS_NEGATIVE = 
//			Elemental.getMethod(VersionPlaceholder.class, "isNegative");
//	static private final Method METHOD_IS_NEGATIVE_INFINITY = 
//			Elemental.getMethod(VersionPlaceholder.class, "isNegativeInfinity");
//	private static final Method METHOD_GET_THREAD_ROLE = 
//			Elemental.getMethod(VersionPlaceholder.class, "getThreadRole");
//	private static final Method METHOD_SET_VERSION = 
//			Elemental.getMethod(VersionPlaceholder.class, "setVersion", Version.class);



	/**
	 * Role-dependent rhs rather than assignable's role-independent one.
	 */
	private Expression rhs = null;
	
	/**
	 * isAssigned && rhs == null => not-yet initialized
	 */
	private Boolean isAssigned = null;
	
	
	
	/**
	 * @param ver
	 * @param isInAST 
	 */
	protected VersionPlaceholder(Version<? extends S> ver, boolean isInAST, Boolean isGlobal, Boolean isAssigned, Expression rhs) {
		super(ver, isInAST, isGlobal);
		
		assert ver != null;
		ver.setGlobal(isGlobal);
//		ver.setAssigner(rhs);
//		setVersion(ver) is invoked via super.setSubject(ver)
		setAssigned(isAssigned, rhs);
	}

	protected VersionPlaceholder(String name, Function<Reference<Version<? extends S>>, Version<? extends S>> verSup, 
			boolean isInAST, Boolean isGlobal, Boolean isAssigned, Expression rhs, VODCondGen condGen) {
		super(name, verSup, isInAST, isGlobal, condGen);
		setAssigned(isAssigned, rhs);
	}



	/**
	 * @return Java name in {@link Name} form.
	 */
	@Override
	public Name getASTName() {
		return get(()-> getAssignable().getASTName(), 
				super::getASTName);
	}

	@SuppressWarnings("unchecked")
	@Override
	public ASTNode getASTAddress() {
		try {
			return trySkipNullException(
					()-> peekASTName(),
//					()-> peekVersion().getASTAddress(),
					VersionEnumerable.super::getASTAddress);
			
		} catch (Exception e) {
			return throwTodoException(e);
		}
	}
	
//	@Override
//	public String getShortAddress() {
//		return getSkipNull(()-> 
//		getAssignable().getShortAddress());
//	}
	
	@Override
	public Assignable<?> getAssignable() {
		return super.guard(
				()-> getNonNull(this::getVersion).getAssignable(),
				()-> null);
	}
	
	/**
	 * @return the effective and possibly previous assigner
	 */
	@Override
	public Expression getAssigner() 
			throws ASTException, UncertainException {
		final Expression asner = AssignableExpression.super.getAssigner();
		return asner == null
				? previousAssigner()	// !isAssigned || isAssigned == null
				: asner;
	}

	@SuppressWarnings("removal")
	@Override
	public Expression getAssignerIf() {
		if (rhs == null) {
			final Assignable<?> asn = getAssignable();
			if (asn == null) return rhs;
			if (asn.isSelfAssigned()) return this;
			
			final Expression sai = AssignableExpression.super.getAssignerIf();
			if (sai != null) setAssigner(tests(sai.isConstant()) 
					? sai 
					: sai.cloneReversion(getPrivatizingBlock(), getThreadRole(), null));	// address != sai.address
		}
		return rhs == null
				? throwTodoException("should have some rhs if assigned")
				: rhs;
	}
		
	@SuppressWarnings("removal")
	@Override
	public void setAssigner(Expression rhs) {
//		if (rhs != null) throwTodoException("inconsistent assignedness");
		if (rhs == null && isInAST()) throwNullArgumentException("rhs");
		
		// rhs.cloneIfChangeRole(getThreadRole())
		if (isPrivate() && !tests(rhs.isConstant()) && !getThreadRole().derives(rhs.getThreadRole())) 
			throwTodoException("underivable rhs");
		
//		if (isInAST()) {
//			final Expression asner = debugGetNonNull(nv, ()-> getAssigner());
//			if (asner instanceof ThreadRoleMatchable) {
//				final ThreadRoleMatchable asnerRm = (ThreadRoleMatchable) asner;
//				if (asnerRm.isPrivate()) {
////					if (newVer.toString().equals("a_THREAD1_1_64_2315_DRB029-truedep1-orig-yes_c")) throwTodoException("debug error");
//					asner.debugRun(()-> newVer.setAssigned(asner.cloneReversion(
//							null, newVer.getThreadRole(), isSelfAssigned() ? (Version<? extends PathVariable>) newVer : null)));
//				} else 
//					newVer.setAssigned(asner);
////				// checking non-address-based version derivation
////				if (asnerRm.derives(newVer) || asnerRm.getThreadRole().derives(nr)) {
////				} else 
////					// functional assigner doesn't derive a master assigned
////					Version.throwNoSuchVersionException(this, nv, asner);
//			} else throwTodoException("unsupported assigner");
//		}

		this.rhs = rhs;
		AssignableExpression.super.setAssigner(rhs);
	}
	
	@Override
	public Boolean isAssigned() {
		if (isAssigned == null && getAssignable() != null) 
			setAssigned(AssignableExpression.super.isAssigned());
		return isAssigned;
	}
	
	@Override
	public boolean isSelfAssigned() {
		return tests(()-> 
		getAssignable().isSelfAssigned());
	}
	
	@Override
	public void setAssigned(Boolean isAssigned) {
		this.isAssigned = isAssigned;
	}
	
	@SuppressWarnings("removal")
	private void setAssigned(Boolean isAssigned, Expression rhs) {
		if (isAssigned != null && isAssigned) {
			if (rhs == null && isInAST()) throwTodoException("inconsistent assigned-ness");
			setAssigner(rhs);
		} else {	// isAssigned == null || !isAssigned
			if (rhs != null) throwTodoException("inconsistent assigned-ness");
		}
		setAssigned(isAssigned);
	}
	

	
	/**
	 * @see fozu.ca.condition.Reference#cacheDirectVariableReferences(Class)
	 * @return singleton set of either version or placeholder
	 */
	@SuppressWarnings("unchecked")
	@Override
	protected <T> Set<T> cacheDirectVariableReferences(
			Class<T> refType) {
		if (refType == null) return throwNullArgumentException(
				"reference type");	// return Collections.emptySet();

		try {
			if (refType.equals(Version.class)) {
				final Version<? extends S> ver = getVersion();
				// including version's argument versions
				final Set<T> dvrs = new HashSet<>(guard(
						()-> (Set<T>) ver.getDirectVariableReferences(refType),
						// reentering empty for continuing the initial entering without duplicates
						Collections::emptySet));
				// including version itself
				dvrs.add((T) ver);
				return dvrs;
			}
			if (getClass().asSubclass(refType) != null) 
				return Collections.singleton((T) this);
		} catch (ClassCastException e) {			// refType == VariablePlaceholder, PathVariablePlaceholder...
		} catch (UncertainPlaceholderException e) {	// thrown by getVersion()
		}
		return Collections.emptySet();
	}

	
	
	@SuppressWarnings("removal")
	@Override
	protected void cacheDirectSideEffect() {
		super.cacheDirectSideEffect();
		
		// TODO: indirect side-effect which may have mutex-side-effects
//		for (Version<?> ver : getVersions())
//			orSideEffect(()-> ver.getSideEffect());
		
		final PlatformType t = getType();
		if (t instanceof DataType) {
			final boolean isli = isLoopIterator();
			switch ((DataType) t) {
			case Int:
				if (isli) {
					final Proposition er = ExpressionRange.fromIteratorOf(
							getAssignable().getEnclosingCanonicalLoop(), getRuntimeAddress(), getCondGen());
					final Statement pb = getPrivatizingBlock();
					if (pb == null) andSideEffect(()-> er);
					else {
						andSideEffect(()-> er.cloneReversion(pb, ThreadRole.THREAD1, null));
						andSideEffect(()-> er.cloneReversion(pb, ThreadRole.THREAD2, null));
						andSideEffect(()-> er.cloneReversion(pb, ThreadRole.FUNCTION, null));
					}
				} else 
					andSideEffect(()-> ExpressionRange.from(this, Int.NEGATIVE_INFINITY, Int.POSITIVE_INFINITY));
				break;
				
			case Real:
				if (isli) throwTodoException("non-canonical loop iterator");
				andSideEffect(()-> ExpressionRange.from(this, Real.NEGATIVE_INFINITY, Real.POSITIVE_INFINITY));
				break;
				
			case Bool, Char, Void:
			default:
				break; 
			}
		}
	}
	
	
	
	@Override
	public List<Statement> getDependentLoops() {
		return getSkipNull(()-> getAssignable().getDependentLoops());
	}

	@Override
	public String getID(SerialFormat format) {
		assert getSubject() != null;
		return getSubject().getID(format);
//		switch (format) {
//		case Z3_SMT: 
//		default:
//		}
//		return getSubject().toNonEmptyString(true);
	}
	
	@Override
	public String getIDSuffix(SerialFormat format) {
		return "_" + getShortAddress(format);
	}

	/**
	 * Placeholder type is directly related to the pointing/sub-array level of
	 * its correspondent {@link Assignable}, not related to its currently 
	 * representing {@link Version}'s type since the type property of 
	 * {@link Version} equals the one of its subject {@link Variable} and 
	 * may be changed due to functional-ization.
	 * 
	 * Setting type by the assignable at construction time is not enough 
	 * since later getting type still calls Reference's one if not overridden.
	 * 
	 * @see fozu.ca.condition.Reference#getType()
	 */
	@SuppressWarnings("removal")
	@Override
	public PlatformType getType() {
		return debugGet(()-> getReferenceableType(), 
				e-> setType());
	}
	
	@SuppressWarnings("removal")
	private PlatformType setType() {
		final PlatformType at = guard(
				()-> getAssignable().getType(),
				()-> getVersion().getType());
		if (at == null) throwTodoException("unsupported assignable type");
		else super.setType(at);
		return at;
//		return at instanceof PointerType ? ((PointerType) at).getType() : at;
	}
	
	@SuppressWarnings("removal")
	@Override
	public void setType(PlatformType newType) {
		super.setType(newType);
		if (hasAssignable() && !newType.equals(getAssignable().getType())) 
			throwTodoException("inconsistent assignable type");
	}
	
	
	
	@SuppressWarnings({ "unchecked", "removal" })
	@Override
	public FunctionallableRole getThreadRole() 
			throws IncomparableException, UncertainPlaceholderException {
		try {
			return trySkipNullException(
					this::peekThreadRole,
					()-> getVersion().getThreadRole(),
					AssignableExpression.super::getThreadRole);
			
		} catch (IncomparableException
				| UncertainPlaceholderException e) {	
			// UncertainPlaceholderException is thrown by recursive placeholder initialization
			throw e;
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
	public FunctionallableRole peekThreadRole() {
		return getSkipNull(()-> peekVersion().getThreadRole());
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public Version<S> peekVersion() {
		return (Version<S>) peekSubject();
	}
	
	/**
	 * @return the current version referenced
	 * @throws ReenterException
	 * @throws IncomparableException
	 * @throws UncertainPlaceholderException
	 */
	@SuppressWarnings({ "unchecked", "removal" })
	@Override
	public Version<S> getVersion() 
			throws ReenterException, IncomparableException, UncertainPlaceholderException {
		try {
			final Version<? extends S> sbj = super.getSubject();
			setVersion(sbj);
			return (Version<S>) sbj;
			
		} catch (ReenterException 
				| IncomparableException 
				| UncertainPlaceholderException e) {	
			throw e;
//		} catch (UncertainException e) {	// thrown by recursive (subject) initialization
//			throw new UncertainPlaceholderException("Re-entering getSubject()", e, this);
		} catch (Exception e) {				
			return throwUnhandledException(e);
//			return null;					// version is initialized to null
		}
	}

	/**
	 * The referenced subject version may be changed (not just appended) to a new one.
	 * That's why we need a delegate to play a constant (place-holder) role, which 
	 * refers changing variable versions, for an {@link Expression}.
	 * 
	 * This method doesn't do subversion-ing.
	 * 
	 * @param newVer the currentVersion to set
	 * @throws NoSuchVersionException 
	 */
	@Override
	@SuppressWarnings({ "unchecked", "removal" })
	public void setVersion(Version<? extends S> newVer) throws NoSuchVersionException {
		// checks no role-matching for allowing role-overriding
		if (!matches(newVer)) throwTodoException("unmatching version");
		
		final Version<S> cv = peekVersion();
		if (cv == newVer) return;

		// derivable (different version class) reversion
		final Version<S> nv = (Version<S>) newVer;
		if (cv != null && nv.derives(cv)) return;	// nv => cv then keeping cv
			
//		// bypassing reentered/recursive version initialization
//		if (!enters(METHOD_SET_VERSION)) try {	
//			enter(METHOD_SET_VERSION);
//			leave(METHOD_SET_VERSION);
//		} catch (ReenterException | UncertainPlaceholderException e) {	
//			/* thrown by recursive (subject) 'initialization' 
//			 * (including initVersion()), which has no versions to set
//			 */
//			e.leave();
//		} catch (NoSuchVersionException e) {
//			throw e;
//		} catch (Exception e) {
//			throwUnhandledException(e);
//		}
		
		super.setSubject(nv);
		if (!newVer.isAddressable()) nv.setAddress(this);
		if (tests(newVer.isGlobal())) setGlobal();
		setConstant(newVer.isConstant());
		setScope(newVer::getScope);
//		setFunctionScope(newVer.getFunctionScope());
		setDirty();
	}

	/**
	 * @return the direct version reference but not indirect variable/function subject
	 */
	@Override
	public final Version<? extends S> getSubject() {
		return getVersion();
	}
	
	@Override
	public final Version<? extends S> setSubject(
			Version<? extends S> newSubject) {
		setVersion(newSubject);
		return newSubject;
	}
	
	@Override
	public void reversion(Version<? extends S> newVersion) throws NoSuchVersionException {
		setVersion(newVersion);
	}
	

	
	@Override
	public boolean containsArithmetic() {
		return getVersion().containsArithmetic();
	}

	
	
	@Override
	protected Boolean cacheConstant() {
		return guard(()-> get(
				()-> getAssignable().isConstant(),
				()-> getVersion().isConstant()));
	}
	
	@Override
	public boolean derives(ThreadRoleMatchable matchable2) {
		boolean result = false;
		if (matchable2 instanceof VersionPlaceholder) 
			result = tests(()-> getAssignable().derives(((VersionPlaceholder<?>) matchable2).getAssignable()));
		return result ? result : super.derives(matchable2);
	}

	@Override
	public boolean isDeclarator() {
		return testsAnySkipNull(
				this::isParameter,
				()-> getAssignable().isDeclarator(),
				()-> getVersion().isDeclarator());	// non-AST declarator
	}
	
	public Boolean isDirectlyFunctional() {
		return get(()-> getAssignable().isDirectlyFunctional(),
				()-> false);	// non-pv -> never functional
	}
	
	/**
	 * @return false always since its assignable should never be null.
	 * @see fozu.ca.vodcg.condition.Referenceable#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		return getAssignable() == null && super.isEmpty();
	}
	
//	@Override
//	public boolean isSemanticallyEmpty() {
//		return getAssignable() == null || super.isEmpty();
//	}
	
//	@Override
//	public boolean isInAST() {
//		return get(()-> peekVersion().isInAST(),
//				()-> super.isInAST());
//	}

	public boolean isIteratorOf(ForStatement loop) {
		return get(()-> getAssignable().isIteratorOf(loop),
				()-> false);
	}
	
	@Override
	public boolean isLoopIterator() {
		return get(()-> getAssignable().isLoopIterator(),
				()-> false);
	}
	
	@Override
	public boolean isParameter() {
		return get(()-> getAssignable().isParameter(),
				()-> false);
	}
	
	
	
	/**
	 * Faster checking for both constant and non-constant variables.
	 * @see fozu.ca.vodcg.condition.ArithmeticExpression#isPositive()
	 */
	@Override
	public Boolean isPositive() {
		final Boolean sip = AssignableExpression.super.isPositive();
		final Boolean isC = isConstant();
		if (sip != null) return sip;
		
		if (isLoopIterator()) return ArithmeticExpression.fromLowerBoundOf(
				getAssignable().getIteratingCanonicalLoop(), getRuntimeAddress(), getCondGen())
				.isPositive();
		// TODO: pAsn > 0 && asn++ 
		// TODO: pAsn > 0 && asn += const
		
		if (isC == null) return get(()-> getVersion().isPositive(),
				e-> null);
		// asn = const
		if (isC) {
			final Expression asgn = getAssigner();
			return asgn instanceof NumericExpression 
					? ((NumericExpression) asgn).isPositive()
					: null;	// for Boolean constants, etc.
		} else return null;	// !isC
		
//		return guardSkipException(()-> 
//		super.isPositive(), METHOD_IS_POSITIVE);
	}
	
	/**
	 * Faster checking for both constant and non-constant variables.
	 * @see fozu.ca.vodcg.condition.ArithmeticExpression#isPositiveInfinity()
	 */
	@Override
	public Boolean isPositiveInfinity() {
		if (isLoopIterator()) {
			final ForStatement loop = getAssignable().getIteratingCanonicalLoop();
			final VODCondGen cg = getCondGen();
			return testsAnySkipNullException(
					()-> ArithmeticExpression.fromLowerBoundOf(loop, getRuntimeAddress(), cg).isPositiveInfinity());
		}
		
		return get(AssignableExpression.super::isPositiveInfinity,
				()-> getVersion().isPositiveInfinity());
	}
	
	/**
	 * Faster checking for both constant and non-constant variables.
	 * @see fozu.ca.vodcg.condition.ArithmeticExpression#isNegative()
	 */
	@Override
	public Boolean isNegative() {
		final Boolean sin = AssignableExpression.super.isNegative();
		final Boolean isC = isConstant();
		if (sin != null) return sin;
		
		if (isC == null) {
			if (isLoopIterator()) return ArithmeticExpression.fromUpperBoundOf(
					getAssignable().getIteratingCanonicalLoop(), getRuntimeAddress(), getCondGen()).isNegative();
			return get(()-> getVersion().isNegative(),
					e-> null);
		
		} else if (isC) {	// asn = -const
			final Expression asgn = getAssigner();
			return asgn instanceof NumericExpression 
					? ((NumericExpression) asgn).isNegative()
					: null;	// for Boolean constants, etc.
		}
		else return sin;	// !isC
	}
	
	/**
	 * Faster checking for constant and non-constant variables.
	 * @see fozu.ca.vodcg.condition.ArithmeticExpression#isNegativeInfinity()
	 */
	@Override
	public Boolean isNegativeInfinity() {
		if (isLoopIterator()) {
			final ForStatement loop = getAssignable().getIteratingCanonicalLoop();
			final VODCondGen cg = getCondGen();
			return testsAnySkipNullException(
					()-> ArithmeticExpression.fromUpperBoundOf(loop, getRuntimeAddress(), cg).isNegativeInfinity());
		}
		
		return get(()-> tests(isConstant()) ? null : getVersion().isNegativeInfinity(),
				AssignableExpression.super::isNegativeInfinity);
	}
	
	
	
	/**
	 * @return true only possibly if it's type is primitive. 
	 */
	@SuppressWarnings("removal")
	@Override
	public Boolean isZero() throws ASTException {
		final Boolean siz = debugGet(AssignableExpression.super::isZero);
		if (siz != null) return siz;
		
		try {
			return getVersion().isZero();
			
		} catch (ASTException e) {
			throw e;
		} catch (IncomparableException e) {		
			// thrown by some (direct/indirect) ASTException catchers
			return null;
		} catch (ReenterException | UncertainPlaceholderException e) {		
			// thrown by recursive version initialization
			return e.leave();
			
		} catch (Exception e) {				
			return throwUnhandledException(e);
		}
	}

	
	
	@Override
	public boolean isLoopIteratingIterator() {
		return getVersion().getAddress().isLoopIteratingIterator();
	}
	
	@Override
	public boolean isLoopInitializedIterator() {
		return getVersion().getAddress().isLoopInitializedIterator();
	}
	
	@Override
	public boolean isZ3ArrayAccess() {
		return getVersion().isZ3ArrayAccess();
	}
	
	
	
	@Override
	public Boolean dependsOn(Expression e) {
		if (tests(super.dependsOn(e))) return true;	// e == this
		if (rhs != this && tests(rhs.dependsOn(e))) return true;	
		
		// assigner dependency
		final Expression asner = getAssigner();
		if (asner != null && asner != this && Boolean.TRUE.equals(asner.dependsOn(e))) return true;			
		
		// asner == null => non-initialized
		// self local dependency
		if (e instanceof VersionPlaceholder) {
			final NavigableSet<VersionPlaceholder<S>> prs = previousRuntimes();
			return prs != null && prs.contains(e);
		}
		return false;
	}
	
	public boolean matches(Version<? extends S> newVer) {
		if (newVer == null) return false;
		
		final Version<? extends S> cv = peekVersion();
		if (cv == null) {
//			if (newVer.isZ3ArrayAccess())
//				// inconsistent assignables
//				if (getAssignable() != newVer.getAssignable()) 
//					return false;
		} else {
			if (!cv.derives((ThreadRoleMatchable) newVer)) 		// cv => nv then setting nv
//			if (!cv.matches(nv.getThreadRole()) || !cv.matches(nv.getExtendedRole())) 
				return false;
				
//			final ThreadRoleMatchable cr = cv.getThreadRole();
//			if (!nv.matches(cr)) Version.throwNoSuchVersionException(cr);
//				
//			// same version class role reversion
//			if (!nv.getClass().equals(cv.getClass())) 
//				throwTodoException("unmatching version class", null, METHOD_SET_VERSION);
		}
		return true;
	}
	
	
	
	@SuppressWarnings("unchecked")
	@Override
	protected boolean equalsToCache(SystemElement e2) {
		return get(()-> peekVersion().equals(((VersionPlaceholder<Referenceable>) e2).peekVersion()),
				()-> equalsObject(e2));
	}

	@SuppressWarnings("removal")
	@Override
	protected List<Integer> hashCodeVars() {
		return debugGet(()-> peekVersion().hashCodeVars(),
				()-> hashCodeObject());
	}
	

	
	@SuppressWarnings("removal")
	@Override
	public Expression negate() {
		final PlatformType t = getType();
		if (t instanceof DataType) switch ((DataType) t) {
		case Bool:		return toProposition().not();
		case Int, Real:	return get(super::negate, 
				e-> AssignableExpression.super.negate());
		default:	
		}
		
		return throwTodoException("unsupported variable type");
	}
	
	
	
	@SuppressWarnings({ "unchecked", "removal" })
	@Override
	public <T extends Addressable> T previous() {
		if (isInAST()) return (T) getAssignable().previous().getPathVariablePlaceholder();
		
		final T pv = getVersion().previous();
		return pv == null
				? pv
				: throwTodoException("unsupported version placeholder");
	}

	/**
	 * @return the latest effective assigner -
	 * 	the <em>semantically</em> previously assigned placeholder's assigner expression.
	 */
	@SuppressWarnings("removal")
	public Expression previousAssigner() 
			throws ASTException, UncertainException {
		final VersionPlaceholder<S> p = previous();
		if (p == this && !tests(isSelfAssigned())) throwTodoException("inconsistent previous");
		if (p == null) return null;
		
		return debugGet(p::getAssigner);
	}
	
	
	
	@SuppressWarnings("removal")
	@Override
	public String toNonEmptyString(boolean usesParenthesesAlready) {
		return debugGet(()-> peekVersion().toNonEmptyString(usesParenthesesAlready),
				()-> getName());
	}


	
	/**
	 * @return @NotNull maybe empty however string.
	 */
	@SuppressWarnings("removal")
	@Override
	public String toZ3SmtString(boolean printsVariableDeclaration, 
			boolean printsFunctionDefinition, boolean isLhs) {
		try {
			return getNonNull(()-> 
			getVersion().toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, isLhs));
			
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}

}