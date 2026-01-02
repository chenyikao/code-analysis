/**
 * 
 */
package fozu.ca.vodcg;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;

import org.eclipse.jdt.core.dom.IASTBinaryExpression;
import org.eclipse.jdt.core.dom.IASTDeclarator;
import org.eclipse.jdt.core.dom.VariableDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationExpression;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.IASTFunctionCallExpression;
import org.eclipse.jdt.core.dom.IASTInitializerList;
import org.eclipse.jdt.core.dom.IASTName;
import org.eclipse.jdt.core.dom.IASTNode;
import org.eclipse.jdt.core.dom.IASTUnaryExpression;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.PostfixExpression;
import org.eclipse.jdt.core.dom.PrefixExpression;

import fozu.ca.Elemental;
import fozu.ca.vodcg.condition.ArithmeticExpression;
import fozu.ca.vodcg.condition.Equality;
import fozu.ca.vodcg.condition.Expression;
import fozu.ca.vodcg.condition.Function;
import fozu.ca.vodcg.condition.FunctionCall;
import fozu.ca.vodcg.condition.PathVariablePlaceholder;
import fozu.ca.vodcg.condition.Proposition;
import fozu.ca.vodcg.condition.VariablePlaceholder;
import fozu.ca.vodcg.util.ASTAssignableComputer;
import fozu.ca.vodcg.util.ASTLoopUtil;
import fozu.ca.vodcg.util.ASTUtil;
import fozu.ca.vodcg.util.IASTDeclaration;
import fozu.ca.vodcg.util.IASTDeclarationStatement;
import fozu.ca.vodcg.util.IASTEqualsInitializer;
import fozu.ca.vodcg.util.IASTInitializer;
import fozu.ca.vodcg.util.IASTSimpleDeclaration;
import fozu.ca.vodcg.util.ASTLoopUtil.Fragment;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public class Assignment extends SystemElement {

	// union structure: assert !(asmAsm != null && asmDcl != null);
	private org.eclipse.jdt.core.dom.Expression asmAsm = null;
	private VariableDeclaration asmDcl = null;
	private Proposition asmEq = null;
	
	private final Set<Assignable<?>> asds = new HashSet<>();
	private final Set<Assignable<?>> asns = new HashSet<>();
	
	private Assignment(org.eclipse.jdt.core.dom.Assignment clause, final ASTAddressable dynaAddr, VODCondGen condGen) {
		super(dynaAddr, condGen);
		asmAsm = clause;
	}

	private Assignment(VariableDeclaration init, final ASTAddressable dynaAddr, VODCondGen condGen) {
		super(dynaAddr, condGen);
		asmDcl = init;
	}



	@SuppressWarnings("unchecked")
    public static List<Assignment> from(ForStatement loop, final ASTAddressable dynaAddr, VODCondGen condGen) {
		if (loop == null) throwNullArgumentException("loop");
		
		final List<Assignment> asms = new ArrayList<>();  // TODO: cache asms
		
		final VariableDeclarationExpression izs = ASTLoopUtil.getCanonicalInitializersOf(loop);
        for (final VariableDeclarationFragment vdf : (List<VariableDeclarationFragment>) izs.fragments()) {
//            final IASTDeclaration idn = ((IASTDeclarationStatement) iz).getDeclaration();
//            if (idn instanceof IASTSimpleDeclaration) {
//                final Name itn = ASTUtil.getNameOf(getSingleIteratorOf(loop, Fragment.initializers));
//                for (IASTDeclarator id : ((IASTSimpleDeclaration) idn).getDeclarators()) 
//                    if (ASTUtil.equals(itn, id.getName(), true)) {
//                        final IASTInitializer i = id.getInitializer();
//                        if (i instanceof IASTEqualsInitializer) 
//                            izs = ((IASTEqualsInitializer) i).getInitializerClause();
//                    }
//            }
            asms.add(new Assignment(vdf, dynaAddr, condGen));
        }
		return asms;
	}
	
	public static Assignment from(VariableDeclaration init, final ASTAddressable dynaAddr, VODCondGen condGen) {
		if (init == null) throwNullArgumentException("initializer");
		return new Assignment(init, dynaAddr, condGen);
	}
	
	/**
	 * @param clause
	 * @param assigned - possibly a function call argument
	 * @param condGen
	 * @return
	 */
	public static Assignment from(
			final org.eclipse.jdt.core.dom.Assignment clause, final Assignable<?> assigned, final VODCondGen condGen) 
			throws UncertainPlaceholderException {
		if (clause == null) throwNullArgumentException("clause");
		if (assigned == null) throwNullArgumentException("assigned");

		final ASTAddressable dynaAddr = assigned.cacheRuntimeAddress();
		final org.eclipse.jdt.core.dom.Expression asdExp = assigned.getExpressionView();
		if (ASTAssignableComputer.isAssignedIn(asdExp, clause)
				|| ASTAssignableComputer.isAssigningIn(asdExp, clause)) 
			return new Assignment(clause, dynaAddr, condGen);
		
		if (ASTAssignableComputer.isLikeAssignment(clause)) 
			return from(ASTUtil.getEnclosingFunctionCallOf(clause), assigned, condGen);
		
		return null;
	}

	/**
	 * @param call
	 * @param arg
	 * @param condGen
	 * @return
	 */
	static public Assignment from(
			final IASTFunctionCallExpression call, final Assignable<?> arg, final VODCondGen condGen) 
			throws UncertainPlaceholderException {
		if (call == null) throwNullArgumentException("function call expression");
		if (arg == null) throwNullArgumentException("function call argument");

		// TODO: may accept assigned library functions if arguments have assignment side-effect
		if (Function.from(call, arg.cacheRuntimeAddress(), condGen).isInLibrary()) return null;
		
		// traversing function call for arg's assigned-ness
		final ASTAddressable dynaAddr = arg.cacheRuntimeAddress();
		if (!arg.isArrayArgument())	try { 
			assert arg.isCallArgument();
			final VariablePlaceholder<?> param = 
					arg.getEnclosingCallParameter();
//					arg.getEnclosingCall().getParameter(arg);
			if (param instanceof PathVariablePlaceholder) {
				for (Assignable<?> p : Assignable.fromOf(
						((PathVariablePlaceholder) param).getAssignable()
						.getWritingFunctionDefinition(), 
						param.getName(), arg.cacheRuntimeAddress(), condGen)) 
					if (tests(p.isAssigned())) return p.getFirstAssignment();	//new Assignment(call, condGen);
			} else	
				// non-AST parameter causing function call assignment
				if (param.isAssigned()) return new Assignment(call, dynaAddr, condGen);
					
		} catch (ASTException e) {	
			// for ambiguous function definitions, etc.
			return new Assignment(call, dynaAddr, condGen);
		} catch (UncertainPlaceholderException e) {
			throw e;
		} catch (Exception e) {
			throwUnhandledException(e);
		}
		return null;
	}
	
	
	
//	private void init() {
//		getAssigned().setAssignment(this);
//		getAssigners().setAssignment(this);
//	}
	

	
	public Assignable<?> getAssigned() throws ASTException {
		try {collectAssignables();}
		catch (UncertainException e) {
			if (!e.excludesAssigneds()) throwUnhandledException(e);
		}
		
		if (asds.size() == 1) {
			final Assignable<?> asd = asds.iterator().next();
			assert asd != null && tests(asd.isAssigned());
			return asd;
		}
		else if (asds.isEmpty()) 
			return throwTodoException("unsupported assignment");
		return throwTodoException("multiple assigneds");
	}
	
	public Set<Assignable<?>> getAssigneds() throws ASTException {
		collectAssignables();
		return asds;
	}
	
	public List<Expression> getAssigners() throws ASTException {
		final List<Expression> les = new ArrayList<>();
		final org.eclipse.jdt.core.dom.Assignment ic = getAssignerClause();
		final VODCondGen cg = getCondGen();
		final ASTAddressable da = cacheRuntimeAddress();
		
		if (ic instanceof IASTInitializerList) 
			for (org.eclipse.jdt.core.dom.Assignment lic : ((IASTInitializerList) ic).getClauses()) 
				les.add(Expression.fromRecursively(lic, da, cg));
		
		else les.add(Expression.fromRecursively(ic, da, cg));
//		try {
//			les.add(((Equality) toEquality()).getAssigner());
//		} catch (ClassCastException e) {
//			throwTodoException(e);
//		}
		
		return les;
	}
	
	@SuppressWarnings("removal")
    public org.eclipse.jdt.core.dom.Expression getAssignerClause() {
		assert !(asmAsm != null && asmDcl != null);
		
		if (asmDcl != null) return asmDcl.getInitializerClause();
		
		if (asmAsm instanceof PrefixExpression) 
			return ((PrefixExpression) asmAsm).getOperand();     // TODO: +-*/ 1?
		if (asmAsm instanceof PostfixExpression) 
		    return ((PostfixExpression) asmAsm).getOperand();    // TODO: +-*/ 1?

		if (ASTAssignableComputer.isAbbreviatedBinaryAssignment(asmAsm)) 
			return ((org.eclipse.jdt.core.dom.Assignment) asmAsm).getLeftHandSide(); // TODO: +-*/ getRightHandSide()?
		if (ASTAssignableComputer.isPlainBinaryAssignment(asmAsm)) 
			return ((org.eclipse.jdt.core.dom.Assignment) asmAsm).getRightHandSide();
		
		return throwTodoException(asmAsm != null
				? ASTUtil.toStringOf(asmAsm) : "assignment without assigners");
	}

	/**
	 * @return non-null set of assigner assignable's.
	 */
	public Set<Assignable<?>> getAssignerAssignables() 
			throws ASTException, UncertainException {
		try {collectAssignables();}
		catch (UncertainException e) {
			if (!e.excludesAssigners()) throw e;
		}
		// UncertainException e => e.excludesAssigners() 
		//	=> assigners are certain
		
		return asns;
//		final Set<Assignable> asners = new HashSet<>();
//		for (Assignable asn : asns) 
//			if (!asn.isArrayArgument()) asners.add(asn);
//		return asners;
	}
	
	public FunctionCall<?> getCallAssigner() throws ASTException {
		return asmAsm instanceof IASTFunctionCallExpression
				? FunctionCall.fromRecursively(
						(IASTFunctionCallExpression) asmAsm, (Supplier<Proposition>) null, cacheRuntimeAddress(), getCondGen())
				: null;
	}

//	/**
//	 * @return null <em>only if</em> this assignment is not initialized
//	 * 	explicitly.
//	 * @throws ASTException
//	 */
//	public Expression getDirectAssigner() throws ASTException {
//		return applySkipNull(ac->
//		Expression.fromRecursively(ac, getCondGen()),
//		()-> getAssignerClause());
//	}

	
	
	public Function getFunctionScope() {
		final ASTAddressable rtAddr = cacheRuntimeAddress();
		if (asmDcl != null) return Function.getFunctionScopeOf(asmDcl, rtAddr, getCondGen());
		if (asmAsm != null) return Function.getFunctionScopeOf(asmAsm, rtAddr, getCondGen());
		return null;
	}

	
	
	/**
	 * asn-- || --asn || asn -= const || asn += -const
	 * @return
	 */
	@SuppressWarnings("removal")
    public boolean assignsDecreasingly() {
		return !assignsIncreasingly() && !assignsEqually();
	}

	/**
	 * asn -= 0 || asn += 0
	 * @return
	 */
	@SuppressWarnings("removal")
	public boolean assignsEqually() {
	    if (asmAsm == null) return false;
	    if (asmAsm instanceof PrefixExpression) return false; 
	    if (asmAsm instanceof PostfixExpression) return false; 
	    return throwTodoException("unsupported assignment");
	}
	
	/**
	 * asn++ || ++asn || asn += const || asn -= -const
	 * @return
	 */
	@SuppressWarnings("removal")
    public boolean assignsIncreasingly() {
	    if (asmAsm == null) return false;
		if (asmAsm instanceof PrefixExpression) return assignsIncreasingly((PrefixExpression) asmAsm); 
		if (asmAsm instanceof PostfixExpression) return assignsIncreasingly((PostfixExpression) asmAsm); 
		if (asmAsm instanceof org.eclipse.jdt.core.dom.Assignment) return assignsIncreasingly((org.eclipse.jdt.core.dom.Assignment) asmAsm);
		return throwTodoException("unsupported assignment");
	}
	
	/**
	 * ++asn 
	 * @return
	 */
	@SuppressWarnings("removal")
	private boolean assignsIncreasingly(PrefixExpression asm) {
	    PrefixExpression.Operator op = asm.getOperator();
	    if (op == PrefixExpression.Operator.DECREMENT) return false;
	    if (op == PrefixExpression.Operator.INCREMENT) return true;
	    return throwTodoException("unsupported assignment");
	}
	
	/**
	 * asn++
	 * @return
	 */
	@SuppressWarnings("removal")
	private boolean assignsIncreasingly(PostfixExpression asm) {
	    PostfixExpression.Operator op = asm.getOperator();
	    if (op == PostfixExpression.Operator.DECREMENT) return false;
	    if (op == PostfixExpression.Operator.INCREMENT) return true;
	    return throwTodoException("unsupported assignment");
	}
	
    /**
     * asn += const || asn -= -const
     * @return
     */
    @SuppressWarnings("removal")
    private boolean assignsIncreasingly(org.eclipse.jdt.core.dom.Assignment asm) {
        org.eclipse.jdt.core.dom.Assignment.Operator op = asm.getOperator();
        if (op == org.eclipse.jdt.core.dom.Assignment.Operator.ASSIGN) throwTodoException("unsupported assignment");

        final Expression ae = getAssigned().getAssigner();
        if (!(ae instanceof ArithmeticExpression)) return throwTodoException("unsupported assignment");
        final ArithmeticExpression aae = (ArithmeticExpression) ae;
        
        if (op == org.eclipse.jdt.core.dom.Assignment.Operator.MINUS_ASSIGN) return Elemental.tests(aae.isPositive());
        if (op == org.eclipse.jdt.core.dom.Assignment.Operator.PLUS_ASSIGN) return Elemental.tests(aae.isNegative());
        return throwTodoException("unsupported assignment");
    }
    
	private void collectAssignables() 
			throws ASTException, UncertainException {
		assert !(asmAsm != null && asmDcl != null);
		final VODCondGen cg = getCondGen();
		
		if (asmDcl != null) {
			asds.add(Assignable.from(asmDcl.getName(), null, cg));
			asns.addAll(Assignable.fromOf(asmDcl.getInitializerClause(), null, cg));
		}
		
		else if (asmAsm instanceof PrefixExpression) {
		    final Assignable<?> asnd = Assignable.from(
		            ((PrefixExpression) asmAsm).getOperand(), null, cg);
		    asns.add(asnd);
		    asds.add(asnd);
		} 
		else if (asmAsm instanceof PostfixExpression) {
			final Assignable<?> asnd = Assignable.from(
					((PostfixExpression) asmAsm).getOperand(), null, cg);
			asns.add(asnd);
			asds.add(asnd);
		}
		
		else if (asmAsm instanceof org.eclipse.jdt.core.dom.Assignment) {
		    final org.eclipse.jdt.core.dom.Assignment asm = (org.eclipse.jdt.core.dom.Assignment) asmAsm;
			asds.add(Assignable.from(
					asm.getLeftHandSide(), null, cg));
			for (IASTName rhsName : ASTUtil.getDescendantsOfAs(
			        asm.getRightHandSide(), IASTName.class)) try {
				final Assignable<?> rhs = Assignable.from(rhsName, null, cg);
				/* rhsLv == this && asgm is binary 
				 * => lv's not at lhs && lv's not unary-assigned
				 */
				if (rhs != null) asns.add(rhs);
			} catch (ASTException e) {
				throw new UncertainException(e, this).excludeAssigneds();
			}
		}
		
		// non-AST function call assignment
		else if (asmAsm instanceof IASTFunctionCallExpression) {
			final org.eclipse.jdt.core.dom.Assignment[] args = 
					((IASTFunctionCallExpression) asmAsm).getArguments();
			if (args != null) for (org.eclipse.jdt.core.dom.Assignment arg : args) {
				final Assignable<?> argAsn = Assignable.from(arg, null, cg);
				if (argAsn == null) continue;
				if (tests(argAsn.isAssigned())) asds.add(argAsn);
				else asns.add(argAsn);
			}
		}
		
		else if (asmAsm != null) throwTodoException(
				"unsupported assignment " + ASTUtil.toStringOf(asmAsm));
	}
	

	
	public boolean contains(IASTNode node) {
		return (asmAsm != null && asmAsm.contains(node))
				|| (asmDcl != null && asmDcl.contains(node));
	}
	
	@Override
	protected Boolean cacheConstant() {
		return getAssigned().isConstant();
	}
	
	protected boolean equalsToCache(SystemElement se2) throws ClassCastException, NullPointerException {
		final Assignment asm2 = (Assignment) se2;
		return (asmAsm != null && asmAsm.equals(asm2.asmAsm))
				|| (asmDcl != null && asmDcl.equals(asm2.asmDcl));
	}
	
	public boolean selfAssigns() {
		if (isAbbreviatedBinary()) return true;
		
		for (Assignable<?> asd : getAssigneds())
			for (Assignable<?> asnr : getAssignerAssignables())
				if (asnr.equals(asd)) return true;
		return false;
	}
	
	public boolean isUnary() {
		return asmAsm instanceof IASTUnaryExpression
				? ASTAssignableComputer.isAssignment((IASTUnaryExpression) asmAsm) 
				: false;
	}
	
	public boolean isBinary() {
		return isPlainBinary() || isAbbreviatedBinary();
	}
	
	/**
	 * @return
	 */
	public boolean isPlainBinary() {
		return (asmAsm instanceof org.eclipse.jdt.core.dom.Assignment 
				&& ((org.eclipse.jdt.core.dom.Assignment) asmAsm).getOperator() == 
				org.eclipse.jdt.core.dom.Assignment.Operator.ASSIGN)
				|| asmDcl != null;
	}

	public boolean isAbbreviatedBinary() {
		return ASTAssignableComputer.isAbbreviatedBinaryAssignment(asmAsm);
	}
	
	/**
	 * A direct assignment is said <em>assigned by</em> rhs and <em>assigned to</em> lhs.
	 * While a call-by-reference assignment is an indirect one.
	 * 
	 * @return
	 */
	public boolean isDirect() {
		return isUnary() || isBinary();
	}
	
	public boolean isDirectlyAssignedTo(IASTName lhs) {
		return isDirect() 
				&& (asmDcl != null
				? ASTAssignableComputer.isDirectlyAssignedIn(lhs, asmDcl)
				: ASTAssignableComputer.isDirectlyAssignedIn(lhs, asmAsm));
	}
	

	
	public boolean isFunctionCall() {
		return asmAsm instanceof IASTFunctionCallExpression;
	}
	
	/**
	 * @return
	 */
	public IASTNode toASTNode() {
		assert !(asmAsm != null && asmDcl != null);
		if (asmDcl != null) return asmDcl;
		if (asmAsm != null) return asmAsm;
		return null;
	}

	@SuppressWarnings("unchecked")
	@Override
	protected Assignment toConstantIf() {
		return this;
	}
	
//	public org.eclipse.jdt.core.dom.Assignment toClause() {
//		assert !(asmAsm != null && asmDcl != null);
//		return asmDcl != null
//				? asmDcl.getInitializerClause()
//				: asmAsm;
//	}
	
	/**
	 * @return single equality or conjunction of equalities if this is an array assignment
	 * @throws ASTException
	 */
	public Proposition toEquality() throws ASTException {
		if (asmEq != null) return asmEq;
		
		try {
			assert !(asmAsm != null && asmDcl != null);
			final VODCondGen cg = getCondGen();
			return asmEq = asmDcl != null
					? Equality.from(asmDcl, cacheRuntimeAddress(), cg)
					: Proposition.fromRecursivelyWithoutBranching(asmAsm, this, cg);
			
		} catch (ClassCastException e) {
			return throwTodoException(e);
		}
	}
	
	@Override
	public String toString() {
		assert !(asmAsm != null && asmDcl != null);
		if (asmDcl != null) return ASTUtil.toStringOf(asmDcl);
		if (asmAsm != null) return ASTUtil.toStringOf(asmAsm);
		return null;
	}

}