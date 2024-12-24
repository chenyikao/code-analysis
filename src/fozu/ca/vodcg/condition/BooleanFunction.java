/**
 * 
 */
package fozu.ca.vodcg.condition;

import java.lang.reflect.Method;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.IName;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Statement;

import fozu.ca.DuoKeyMap;
import fozu.ca.Elemental;
import fozu.ca.condition.SerialFormat;
import fozu.ca.vodcg.VODCondGen;
import fozu.ca.vodcg.condition.FunctionCall.CallProposition;
import fozu.ca.vodcg.condition.version.ConstantCountingVersion;
import fozu.ca.vodcg.condition.version.FunctionallableRole;
import fozu.ca.vodcg.condition.version.Version;
import fozu.ca.vodcg.condition.version.NoSuchVersionException;
import fozu.ca.vodcg.condition.version.ThreadRoleMatchable;
import fozu.ca.vodcg.condition.version.UniversalVersion;
import fozu.ca.vodcg.condition.version.VersionEnumerable;
import fozu.ca.vodcg.Assignable;
import fozu.ca.vodcg.condition.data.DataType;
import fozu.ca.vodcg.condition.data.Pointer;

/**
 * A BooleanFunction can be
 * 
 * 1) a wrapper of a Bool type function which 
 * 	getType() == DataType.Bool && !instanceof BooleanFunction
 * 
 * 2) a side-effect container, which stores side-effect rather than 
 * 	a pure CallProposition. 
 * 
 * @author Kao, Chen-yi
 *
 */
public class BooleanFunction extends Function 
implements VersionEnumerable<BooleanFunction> {

	private static final String UNSUPPORTED_OPERATION = "unsupported operation";

	private static final Method 
	METHOD_REDUCE_ONCE 	= Elemental.getMethod(BooleanFunction.class, "reduceOnce");
	
	/**
	 * A function may derive many boolean ones according to different side-effect calls.
	 */
	private static final DuoKeyMap<Function, Proposition, BooleanFunction> 
	ALL_BOOL_FUNCTIONS 	= new DuoKeyMap<>();
	
	private static final Map<String, BooleanFunction> 
	HIGHEST_VERSION = new HashMap<>();
	
	
	
	private Function ref = null;
	private final Map<ConditionElement, FunctionCall<BooleanFunction>> virtualCalls = new HashMap<>();
	
//	/**
//	 * version-independent root name
//	 */
//	private String rName = null;
	/**
	 * Each {@link Version<BooleanFunction>} associates with a unique 
	 * boolean function body (side-effect); 
	 * while a {@link Version<Variable>} doesn't.
	 */
	private Version<? extends BooleanFunction> version = null;
	private boolean versionIsLocked = false;

	
	
	/**
	 * @param library 
	 * @param name - version-independent root name
	 * @param rtAddr 
	 * @param scopeManager 
	 */
	private BooleanFunction(String library, String name, VODCondGen scopeManager) {
		super(library, name, DataType.Bool, scopeManager);
//		rName = name;
		
//		if (equalsInPlatformLibrary()) this.name += "_bool";
		increaseCounting();
	}
	
	/**
	 * Wrapper constructor for f.getType() != DataType.Bool, 
	 * which handles side-effects for non-boolean functions.
	 * 
	 * @param f
	 * @param body - non-null means must handle some side-effect 
	 * 	TODO? and there's only a call proposition place-holder default to true, 
	 * 	a partial tautology function making sat locally.
	 * @see FunctionCall.CallProposition 
	 */
	@SuppressWarnings("removal")
	private BooleanFunction(Function f, Proposition body) {
		super(f.getLibrary(), f.getName(), DataType.Bool, f.getScopeManager());
	
		assert f != null && f.getType() != DataType.Bool;
		if (body == null) throwTodoException("unnecessary empty boolean function");
		setBody(body);
		
		ref = f;
		// version-independent root-name
//		if (f.equalsInPlatformLibrary()) name = f.getName() + "_bool";	
		increaseCounting();
	}


	
	@SuppressWarnings("unchecked")
	private void increaseCounting() {
		String fName = getName();
		final BooleanFunction hvf = HIGHEST_VERSION.get(fName);
		
		try {
		if (hvf == null) setVersion(new UniversalVersion<>(this));
		else {
			final Version<? extends BooleanFunction> hv = hvf.version;
			/* Boolean function ID is determined by the version therefore is ambiguous during 
			 * version update and needs to be locked.
			 */
			versionIsLocked = true;
			hvf.versionIsLocked = true;
			if (hv instanceof UniversalVersion) {
				final FunctionallableRole hvr = hv.getThreadRole();
				hvf.setVersion(new ConstantCountingVersion<>(0, hvf, hvr));
				setVersion(new ConstantCountingVersion<>(1, this, hvr));
			}
			else setVersion(((ConstantCountingVersion<BooleanFunction>) hv)
				.cloneByIncreaseCounting(this));	// hvf = hv.getAddress()
			hvf.versionIsLocked = false;
			versionIsLocked = false;
			
//			version.setSubject(this);
//			hvf.version.setSubject(hvf);
		}
		} catch (NoSuchVersionException e) {
			throwTodoException(e);
		}
		
		HIGHEST_VERSION.put(fName, this);
	}
	
	
	
	public static BooleanFunction from(Function f, Proposition body) {
		if (f == null) return throwNullArgumentException("function");
		if (body == null) return throwNullArgumentException("function body");
		
		BooleanFunction bf = ALL_BOOL_FUNCTIONS.get(f, body);
		if (bf == null) {
//			if (sideEffect == null && ALL_BOOL_FUNCTIONS.key1Set().contains(f))
			if (f instanceof BooleanFunction) bf = (BooleanFunction) f;
//			else if (f.getType().equals(DataType.Bool))
//				throwTodoException("truly duplicate boolean function");
			else bf = new BooleanFunction(f, body);
//			bf = new BooleanFunction(f.getLibrary(), f.name, f.getScopeManager());
					
			ALL_BOOL_FUNCTIONS.put(f, body, bf);
		}
		
		return bf;
	}
	
//	public static BooleanFunction from(
//			String library, String name, Supplier<VODCondGen> condGen, Parameter... params) {
//		if (library == null) throwNullArgumentException("library");
//		if (name == null) throwNullArgumentException("name");
//		
//		final String signature = getID(name, params);
//		Function f = LIB_FUNCTIONS.get(library, signature);
//		if (f == null) {
//			LIB_FUNCTIONS.put(
//					library, signature, f = new Function(library, name, type, condGen));
//			f.setParameters(()-> params);
//		}
//		return f;
//	}
	
//	public static BooleanFunction get(Function f, 
//			FunctionCall<BooleanFunction>.CallProposition callProp) {
//		if (f == null || callProp == null) return null;
//		
//		return callProp.getCallFunction();
//	}
	
	
	
	/**
	 * @return All registered boolean functions.
	 */
	public static Set<BooleanFunction> getAll() {
		return ALL_BOOL_FUNCTIONS.valueSet();
	}

	@SuppressWarnings("removal")
	@Override
	public Assignable<?> getAssignable() {
		return throwTodoException("non-assignable");
	}
	
	@Override
	public ASTNode getASTAddress() {
		return getASTName();
	}

	private FunctionCall<BooleanFunction> getCall(
			ConditionElement callScope, Supplier<FunctionCall<BooleanFunction>> callSup) {
		assert callSup != null;
		if (callScope == null) callScope = getCondGen().getGlobalScope();
		
//		virtualCalls.clear();
		FunctionCall<BooleanFunction> c = virtualCalls.get(callScope);
		if (c == null) {
			c = callSup.get();
			virtualCalls.put(callScope, c);
		}
		return c;
	}
	
	/**
	 * @param callName 
	 * @param callScope - null means global scope
	 * @return
	 */
	public FunctionCall<BooleanFunction> getCall(
			IName callName, List<?> args, ConditionElement callScope) {
		return getCall(callScope, 
				()-> new FunctionCall<>(this, callName, args, callScope));
	}
	
	public FunctionCall<BooleanFunction> getCall(
			String callName, List<?> args, ConditionElement callScope) {
		return getCall(callScope, 
				()-> new FunctionCall<>(this, callName, args, callScope));
	}
	
	/**
	 * @param callName 
	 * @param callScope - null means global scope
	 * @return
	 */
	public CallProposition getCallProposition(
			IName callName, List<?> args, ConditionElement callScope) {
		return getCall(callName, args, callScope).getCallProposition();
	}
	
	/**
	 * @param callName 
	 * @param callScope - null means global scope
	 * @return
	 */
	public CallProposition getCallProposition(
			String callName, List<?> args, ConditionElement callScope) {
		return getCall(callName, args, callScope).getCallProposition();
	}
	


//	@Override
//	public NavigableSet<OmpDirective> getEnclosingDirectives() {
//		return null;
//	}
	
	@Override
	public String getID(SerialFormat format) {
		if (versionIsLocked) return null;
		
		String id = isReference() 
				? ref.getID(format) 
				: getName();
		if (version != null) id += version.getIDSuffix(format);
		return id;
	}
	
	/* (non-Javadoc)
	 * @see fozu.ca.condition.Function#getPointers()
	 */
	@Override
	public Set<Pointer> getPointers() {
		return isReference() 
				? ref.getPointers()
				: super.getPointers();
	}
	
	public Function getReference() {
		return ref;
	}
	
	
	
	@Override
	public DataType getType() {
		return DataType.Bool;
	}

	@Override
	public BooleanFunction getVersionSubject() {
		return this;
	}

	@Override
	public Version<? extends BooleanFunction> peekVersion() {
		return version;
	}

	@SuppressWarnings("removal")
	@Override
	public Version<? extends BooleanFunction> peekVersion(ThreadRoleMatchable role) {
		return throwTodoException(UNSUPPORTED_OPERATION);
	}

	@Override
	public void setVersion(Version<? extends BooleanFunction> newVersion) {
		if (newVersion == null) throwNullArgumentException("new version");
		if (newVersion.getSubject() != this) throwInvalidityException("inconsistent subject");
		version = newVersion;
	}

	@Override
	public boolean reversions() {
		return !versionIsLocked;
	}
	
	@SuppressWarnings("removal")
	@Override
	public void reversion(Version<? extends BooleanFunction> newVersion) throws NoSuchVersionException {
		throwTodoException(UNSUPPORTED_OPERATION);
	}
	
	
	
	/* (non-Javadoc)
	 * @see fozu.ca.condition.Function#unwrapOnce()
	 */
	@Override
	public Function reduceOnce() {
		return isReference() 
				? ref.reduce(METHOD_REDUCE_ONCE)
				: super.reduceOnce();
	}
	


	@Override
	@SuppressWarnings({ "unchecked" })
	public void andSideEffect(Supplier<? extends SideEffectElement> newSideEffect) {
		Proposition prop = (Proposition) getBody();
		try {
			setBody(prop == null ? (Proposition) newSideEffect.get() : prop.and((Supplier<Proposition>) newSideEffect));
		} catch (ClassCastException e) {
			throwInvalidityException("non-proposition");
			return;
		}
		super.andSideEffect(()-> getBody());
	}
	
	@Override
	public void andSideEffect(VODConditions newSideEffect) {
		if (newSideEffect == null) return;
		
		andSideEffect(newSideEffect.getPathCondition());
		super.andSideEffect(newSideEffect.getParallelCondition());
	}
	
	@Override
	public void andSideEffect(PathCondition newSideEffect) {
		if (newSideEffect == null) return;
		
		setBody(newSideEffect.getAssertion().get());
	}
	

	
	/**
	 * @param prop
	 */
	public void and(Supplier<Proposition> prop) {
		if (prop == null) throwNullArgumentException("proposition");

		Proposition body = (Proposition) getBody();
		setBody(body == null ? prop.get() : body.and(prop)); 
	}

	public void or(Supplier<Proposition> prop) {
		if (prop == null) return;

		Proposition body = (Proposition) getBody();
		setBody(body == null ? prop.get() : body.or(prop)); 
	}

	/**
	 * @param prop
	 */
	public void xor(Supplier<Proposition> prop) {
		if (prop == null) return;
		
		Proposition body = (Proposition) getBody();
		setBody(body == null ? prop.get() : body.xor(prop)); 
	}
	
	/**
	 * @param consq
	 */
	public void imply(Supplier<Proposition> consq) {
		if (consq == null) return;
		
		Proposition body = (Proposition) getBody();
		if (body == null) return;
		setBody(body.imply(consq)); 
	}
	
	/**
	 * @param prop
	 */
	public void iff(Supplier<Proposition> prop) {
		if (prop == null) return;
		
		Proposition body = (Proposition) getBody();
		if (body == null) return;
		setBody(body.iff(prop)); 
	}
	
	public void not() {
		Proposition body = (Proposition) getBody();
		if (body == null) return;
		setBody(body.not()); 
	}
	
	/* (non-Javadoc)
	 * @see fozu.ca.condition.Function#negate()
	 */
	@Override
	public Expression negate() {
		return isReference() 
				? ref.negate()
				: super.negate();
	}

	
	
	/* (non-Javadoc)
	 * @see fozu.ca.condition.Function#isConstant()
	 */
	@Override
	protected Boolean cacheConstant() {
		return isReference() 
				? ref.isConstant()
						: super.isConstant();
	}
	
	/* (non-Javadoc)
	 * @see fozu.ca.condition.Function#getVariableReferences()
	 */
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
		return isReference() 
				? ref.cacheDirectVariableReferences(refType)
						: super.cacheDirectVariableReferences(refType) ;
	}
	
	@Override
	protected ConditionElement cacheScope() {
		return isReference()
				? ref.getScope()
				: super.cacheScope();
	}
	
	/* (non-Javadoc)
	 * @see fozu.ca.condition.Function#cacheGlobal()
	 */
	@Override
	protected Boolean cacheGlobal() {
		return isReference() ? ref.isGlobal() : super.cacheGlobal();
	}
	
	@SuppressWarnings("removal")
	@Override
	public Boolean isAssigned() {
		return throwTodoException(UNSUPPORTED_OPERATION);
	}
	
	@Override
	public final boolean isBool() {
		return true;
	}
	
	/* (non-Javadoc)
	 * @see fozu.ca.condition.Function#isMain()
	 */
	@Override
	public boolean isMain() {
		return isReference() 
				? ref.isMain()
				: super.isMain();
	}

	public final boolean isReference() {
		return ref != null;
	}
	
//	public int compareTo(Function f2) {
//		if (isReference()) return getReference().compareTo(f2);
//		return super.compareTo(f2);
//	}
	
	/* (non-Javadoc)
	 * @see fozu.ca.condition.Function#equalsFunction(fozu.ca.condition.Function)
	 */
	@Override
	public boolean equalsFunction(Function f2) {
		if (super.equalsFunction(f2)) return true;
		if (isReference()) return ref.equalsFunction(f2);	// reference equal
		return false;
	}
	
	

	/* (non-Javadoc)
	 * @see fozu.ca.condition.Function#toProposition()
	 */
	@Override
	public Proposition toProposition() {
		return (Proposition) getBody();
	}

//	/**
//	 * @see fozu.ca.condition.Function#toSideEffectCall(fozu.ca.condition.Proposition)
//	 */
//	@Override
//	public FunctionCall<BooleanFunction>.CallProposition toSideEffectCall(
//			Proposition newProp) {
//		return isReference() 
//				? ref.toSideEffectCall(newProp)
//				: super.toSideEffectCall(newProp);
//	}

//	/* (non-Javadoc)
//	 * @see fozu.ca.condition.Function#toSideEffectCall(fozu.ca.condition.Proposition.Operator, fozu.ca.condition.Proposition)
//	 */
//	@Override
//	public FunctionCall<BooleanFunction>.CallProposition toSideEffectCall(
//			Operator op, Proposition newProp) {
//		return ref == null 
//				? super.toSideEffectCall(op, newProp) 
//				: ref.toSideEffectCall(op, newProp);
//	}

}