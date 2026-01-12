/**
 * 
 */
package fozu.ca.vodcg.condition;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

import org.eclipse.cdt.core.dom.IName;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IVariable;
import org.eclipse.jdt.core.ILocalVariable;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.Statement;

import fozu.ca.condition.SerialFormat;
import fozu.ca.vodcg.ASTAddressable;
import fozu.ca.vodcg.Assignable;
import fozu.ca.vodcg.VODCondGen;
import fozu.ca.vodcg.condition.data.ArithmeticGuard;
import fozu.ca.vodcg.condition.data.DataType;
import fozu.ca.vodcg.condition.data.PlatformType;
import fozu.ca.vodcg.condition.version.FunctionallableRole;
import fozu.ca.vodcg.condition.version.ThreadRole;
import fozu.ca.vodcg.condition.version.Version;
import fozu.ca.vodcg.util.ASTUtil;

/**
 * @author Kao, Chen-yi
 *
 */
public class Variable extends Referenceable {

//	private static final Method METHOD_FROM_NON_AST = 
//			Elemental.getMethod(Variable.class, "fromNonAST", String.class, PlatformType.class, boolean.class, Supplier.class, Statement.class, Supplier.class);

	/**
	 * Even a non-AST variable may still bind to some AST structure.
	 */
	private Statement astScope = null;
	private Boolean isParam = null;
	
	/**
	 * Non AST variables include the API/library parameters (i.e., boundary path variables)
	 */
	private static final Map<String, Set<Variable>> NON_AST_VARIABLES = 
			new HashMap<>();
	
	/**
	 * Constructor for a non-AST variable.
	 * 
	 * @param name
	 * @param type
	 * @param isParameter - true if it's a non-AST function parameter
	 * @param astScope
	 * @param condGen
	 */
	private Variable(String name, PlatformType type, boolean isParameter,
			Statement astScope, VODCondGen condGen) {
		super(name, type, condGen);
		this.astScope = astScope;
		this.isParam = isParameter;
	}
	
	protected Variable(Name name, PlatformType type, final ASTAddressable rtAddr, VODCondGen condGen) {
		super(name, type, rtAddr, condGen);
	}
	
	protected Variable(Name name, final ASTAddressable rtAddr, VODCondGen condGen) {
		this(name, (PlatformType) null, rtAddr, condGen);
	}
	
//	protected Variable(IASTName name, DataType type) 
//			throws IllegalArgumentException, CoreException, InterruptedException {
//		this(name, type, Function.getScopeOf(name));
//	}
	
	protected Variable(Name name, IBinding bind, final ASTAddressable rtAddr, VODCondGen condGen) {
		super(name, bind, rtAddr, condGen);
	}
	
	public static Variable fromNonAST(String name, PlatformType type, boolean isParameter,
			Supplier<? extends ConditionElement> scope, Statement astScope, VODCondGen condGen) {
		if (scope == null) throwNullArgumentException("scope");

		Set<Variable> vars = NON_AST_VARIABLES.get(name);
		if (vars == null) NON_AST_VARIABLES.put(name, vars = new HashSet<>()); 
		else for (Variable v : vars) 
			if (guardTests(()-> v.getScope() == scope.get())) return v;
			
		final Variable v = new Variable(name, type, isParameter, astScope, condGen);
		// setScope() -> isGlobal() -> funcScope
		v.setScope(scope);
		vars.add(v);	// hashCode depends on funcScope
		return v;
	}

	public static Variable fromNonAST(ILocalVariable var, boolean isParameter,
			Supplier<ConditionElement> scope, Statement astScope, VODCondGen condGen) {
		if (var == null) throwNullArgumentException("AST variable");

		return fromNonAST(var.getName(),
				DataType.from(var.getType()), 
				isParameter, scope, astScope, condGen);
	}

	

	/**
	 * @return
	 * @see #astScope
	 */
	public Statement getASTScope() {
		return astScope;
	}
	
	@Override
	public String getIDSuffix(final SerialFormat format) {
		return debugGetNonNull(()-> isParameter()
				? getFunctionScope().getName()
				: getScope().getIDSuffix(format));
	}
	
	@Override
	public FunctionallableRole getThreadRole() {
		return get(()-> super.getThreadRole(),
				()-> isThreadPrivate() ? ThreadRole.NON_MASTER : ThreadRole.MASTER);
//		return throwUnsupportedRoleException();
	}

	
	
	/**
	 * A variable declaration has no references (instances) for now.
	 * TODO: return ALL path and non-path references to this variable.
	 * 
	 * @see fozu.ca.vodcg.condition.ConditionElement#getDirectVariableReferences()
	 */
	@Override
	protected <T> Set<? extends T> cacheDirectVariableReferences(Class<T> refType) {
		return null;
	}
	
	@Override
	protected Set<ArithmeticGuard> cacheArithmeticGuards() {
		return null;
	}
	
	@Override
	protected Set<Function> cacheDirectFunctionReferences() {
		return null;
	}
	
	/**
	 * A variable declaration has no side effects for now.
	 * TODO: return ALL delegate side effects of this variable.
	 * 
	 * @fozu.caozu.ca.condition.Expression#cacheDirectSideEffect()
	 */
	@Override
	protected void cacheDirectSideEffect() {
	}
	

	
//	/**
//	 * @param lowerBound
//	 * @param upperBound
//	 * @return
//	 */
//	public VariableRange getRangeOf(Expression lowerBound, Expression upperBound) {
//		return VariableRange.get(this, lowerBound, upperBound);
//	}


	
	/**
	 * @param vars1
	 * @param vars2
	 * @return
	 */
	public static boolean conflictsByName(Collection<Version<Variable>> vars1,
			Collection<VariablePlaceholder<?>> vars2) {
		for (Version<Variable> v1 : vars1)
			for (VariablePlaceholder<?> v2d : vars2) {
				@SuppressWarnings("unchecked")
				Version<Variable> v2 = (Version<Variable>) v2d.getSubject();
				if (v1.equalsId(v2, null) && !v1.equals(v2)) return true;
			}
		return false;
	}

	/* (non-Javadoc)
	 *fozu.ca fozu.ca.condition.Expression#containsArithmetic()
	 */
	@Override
	public boolean containsArithmetic() {
		return false;
	}
	

	
	public boolean isParameter() {
		if (isParam != null) return isParam;
		
		final Name cName = getASTName();
		if (cName != null) {
			final Assignable<?> def = Assignable.from(
					ASTUtil.getDefinitionOf(cName), getCondGen());
			if (def != null) return isParam = def.isParameter();
		}
		
		return isParam;
	}

	
	
	@Override
	protected List<Integer> hashCodeVars() {
		final List<Integer> hcvs = new ArrayList<>(super.hashCodeVars());
		hcvs.add(get(()-> astScope.hashCode(), ()-> 0)); 
		hcvs.add(get(()-> isParam.hashCode(), ()-> 0));
//		hcvs.add(get(()-> getFunctionScope().hashCode(), ()-> 0));
		return hcvs;
	}

	
	
	/**
	 * TODO: A variable (not reference) negation means ALL possible references to it SHOULD be negated.
	 * 
	fozu.caee fozu.ca.condition.Expression#negate()
	 */
	@Override
	public Expression negate() {
		return null;
	}

	
	
	@Override
	public void setFunctionScope(Supplier<Function> scope) {
		if (scope == null && isParameter()) 
			throwInvalidityException("non-global parameter");
		super.setFunctionScope(scope);
	}

	
	
	protected String toNonEmptyString(boolean usesParenAlready) {
		return getName();
	}
	
	/** 
	 * For parameter declaration.fozu.ca@see fozu.ca.condition.Referenceable#toZ3SmtString(boolean, boolean, boolean)
	 */
	@Override
	public String toZ3SmtString(boolean printsVariableDeclaration, 
			boolean printsFunctionDefinition, boolean isLhs) {
		final String id = super.toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition, isLhs);
		if (printsFunctionDefinition) return 
				"(" + id + " " + 
				getType().toZ3SmtString(printsVariableDeclaration, printsFunctionDefinition) +
				")";
		return id;
	}

}