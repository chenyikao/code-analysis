/**
 * 
 */
package fozu.ca.vodcg;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.jdt.core.dom.IASTDeclarator;
import org.eclipse.jdt.core.dom.IASTFunctionDeclarator;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.VariableDeclaration;
import org.eclipse.jdt.core.dom.IFunction;
import org.eclipse.jdt.core.dom.IMethodBinding;

import fozu.ca.Elemental;
import fozu.ca.vodcg.condition.ArithmeticExpression;
import fozu.ca.vodcg.condition.Expression;
import fozu.ca.vodcg.condition.Function;
import fozu.ca.vodcg.condition.FunctionCall;
import fozu.ca.vodcg.condition.FunctionalPathVariable;
import fozu.ca.vodcg.condition.PathVariablePlaceholder;
import fozu.ca.vodcg.condition.data.PlatformType;
import fozu.ca.vodcg.util.ASTUtil;

/**
 * A FunctionAssignable represents <em>only</em> an AST function name.
 * It is more restricted than a functional assignable, which may also represents an AST array name.
 * 
 * @author Kao, Chen-yi
 *
 */
public class FunctionAssignable extends Assignable<FunctionalPathVariable> {
//implements VersionEnumerable<FunctionalPathVariable> {

	private FunctionCall<?> call = null;
	
	protected FunctionAssignable(
			Name name, IMethodBinding bind, /*VariableDeclaration variableDeclaration,*/ final ASTAddressable rtAddr, VODCondGen condGen) 
					throws ASTException {
		super(name, bind, /*variableDeclaration,*/ rtAddr, condGen);
	}
	
	
	
	@Override
	public Set<Assignable<?>> getArguments() {
		// function call
		if (isCall()) {
			final Set<Assignable<?>> args = new HashSet<>();
			for (Expression arg : getCallView().getArguments())
				for (PathVariablePlaceholder pvp : 
					arg.getDirectPathVariablePlaceholders())
					args.add(pvp.getAssignable());
			return args;
		}
		
		// function declaration
		return Collections.emptySet();
	}
	
	@Override
	public List<ArithmeticExpression> getFunctionalArguments() {
		if (!isCall()) return null;
		
		final List<ArithmeticExpression> args = new ArrayList<>();
		for (Expression arg : getEnclosingCall().getArguments()) {
			if (arg instanceof ArithmeticExpression) args.add((ArithmeticExpression) arg);
			else throwTodoException("unsupported argument type");
		}
		return args;
	}
	
	public FunctionCall<?> getCallView() {
		return getEnclosingCall();
	}
	
	/**
	 * @return non-null since a function assignable must have a function call
	 */
	@Override
	public FunctionCall<?> getEnclosingCall() throws ASTException {
		if (call != null) return call;
		return call = getNonNull(()-> super.getEnclosingCall());
	}
	
	/**
	 * Non-recursive and run-once checking in the initialization.
	 * @return
	 */
	public boolean isCall() {
		return getCallView() != null;
	}
	
	public Function getFunction() {
		return Function.from((IFunction) getBinding(), cacheRuntimeAddress(), getCondGen());
	}
	
	@Override
	public Set<Assignable<?>> getDirectAssigners() {
		return Collections.emptySet();
//		if (!isCall()) return isASTFunction() ?
//				Collections.emptySet() : super.getDirectAssigners();
//		
//		// !isAssigned()
//		final Set<Assignable<?>> asgrs = new HashSet<>();
//		for (PathVariablePlaceholder v : 
//			getCallView().getDirectPathVariablePlaceholders())
//			asgrs.add(v.getAssignable());
//		return asgrs;
	}
		
	protected Set<Assignable<?>> getNonASTFunctionDirectAssigners() {
		return super.getDirectAssigners();
	}
	
//	@Override
//	public Set<Version<Variable>> getDirectVariableReferences() {
//		return getCallView().getDirectVariableReferences();
//	}
	
//	@Override
//	public PathVariablePlaceholder getPathVariablePlaceholder() {
//		return null;
//	}
	
//	@Override
//	public VODConditions getConditions(final String progress) 
//			throws ASTException {
//		// a function call does NOT necessarily have lhs
//		return isCall() 
//				? getCallView().getSideEffect() 
//				: super.getConditions(progress);
//	}
	
	@Override
	public PlatformType getType() {
		final PlatformType t = super.getType();
		if (t != null) return t;
		return isCall() 
				? getCallView().getType() 
				: getFunction().getType();
	}

	
	
	@Override
	protected Boolean cacheConstant() {
		// !isAssigned()
		for(Assignable<?> asgn : getDirectAssigners()) {
			if (equalsVariable(asgn)) return false;		// recursive call
			if (Elemental.testsNot(asgn.isConstant())) return false;
		}
		
		// isFunctionCall() => no arguments
		return getFunction().isConstant();
	}

	@Override
	protected Assignable<FunctionalPathVariable> toConstantIf() throws ASTException, UncertainException {
		return this;
	}
	
	/**
	 * @return true if this assignable represents a function name or call name.
	 */
	@Override
	public boolean isASTFunction() {
		assert super.isASTFunction();
		return true;
	}
	
	/**
	 * The AST function needs not be functional again
	 */
	@Override
	public Boolean isFunctional() {
		return false;
	}
	
//	/**
//	 * The AST function needs not be functional again
//	 */
//	@Override
//	public Boolean isDirectlyFunctional() {
//		return false;
//	}
	
	public Boolean isDirectlyConstant() {
		return cacheConstant();
	}
	
	@SuppressWarnings("unchecked")
	public boolean isDeclaration() {
		return getVariableDeclaration() != null 
				&& ASTUtil.getAncestorOfAsUnless(getVariableDeclaration(), 
						new Class[]{IASTFunctionDeclarator.class},
						ASTUtil.AST_FUNCTION_DEFINITION, 
						false) != null;
	}
	
	@Override
	public boolean isRuntimeTraversable() {
		return !isDeclaration();
	}
	
	/**
	 * @return true if it represents a locally declared function.
	 */
	@Override
	public boolean isThreadPrivate() {
		if (super.isThreadPrivate())
			return isArray() ? isDirectiveLocal() : true;
		return false;
	}
	
//	/**
//	 * A function call may have multiple self-assigning/assigned (array arguments).
//	 */
//	@Override
//	public boolean isSelfAssigning() {
//		return isFunctionCall() && ;
//	}
	
//	@Override
//	public Assignable previousRuntimeAssigned() {
//		return throwTodoException("conditional function call placeholder");
//	}
	
}