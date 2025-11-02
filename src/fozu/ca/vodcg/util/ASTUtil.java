/**
 * 
 */
package fozu.ca.vodcg.util;

import java.io.File;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.jdt.core.CCorePlugin;
import org.eclipse.jdt.core.Flags;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTGenericVisitor;
import org.eclipse.jdt.core.dom.ASTNameCollector;
import org.eclipse.jdt.core.dom.ASTSignatureUtil;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.DOMException;
import org.eclipse.jdt.core.dom.EScopeKind;
import org.eclipse.jdt.core.dom.ArrayAccess;
import org.eclipse.jdt.core.dom.ChildListPropertyDescriptor;
import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.SwitchCase;
import org.eclipse.jdt.core.dom.Comment;
import org.eclipse.jdt.core.dom.DoStatement;
import org.eclipse.jdt.core.dom.IASTEqualsInitializer;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.IASTFileLocation;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.IfStatement;
import org.eclipse.jdt.core.dom.IASTInitializerClause;
import org.eclipse.jdt.core.dom.IASTLiteralExpression;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.IASTNameOwner;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.IASTNodeLocation;
import org.eclipse.jdt.core.dom.Annotation;
import org.eclipse.jdt.core.dom.IASTPreprocessorStatement;
import org.eclipse.jdt.core.dom.ReturnStatement;
import org.eclipse.jdt.core.dom.Statement;
import org.eclipse.jdt.core.dom.StructuralPropertyDescriptor;
import org.eclipse.jdt.core.dom.IASTSwitchStatement;
import org.eclipse.jdt.core.dom.IASTTranslationUnit;
import org.eclipse.jdt.core.dom.IASTUnaryExpression;
import org.eclipse.jdt.core.dom.WhileStatement;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IEnumeration;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.IParameter;
import org.eclipse.jdt.core.dom.IProblemBinding;
import org.eclipse.jdt.core.dom.IType;
import org.eclipse.jdt.core.index.IIndex;
import org.eclipse.jdt.core.index.IIndexBinding;
import org.eclipse.jdt.core.index.IIndexManager;
import org.eclipse.jdt.core.index.IndexFilter;
import org.eclipse.jdt.core.model.CoreModel;
import org.eclipse.jdt.core.model.CoreModelUtil;
import org.eclipse.jdt.core.model.ICProject;
import org.eclipse.jdt.core.model.ITranslationUnit;
import org.eclipse.jdt.internal.compiler.GenericAstVisitor;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;

import fozu.ca.DebugElement;
import fozu.ca.DuoKeyMap;
import fozu.ca.Elemental;
import fozu.ca.vodcg.ASTException;
import fozu.ca.vodcg.SystemElement;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("deprecation")
public final class ASTUtil extends DebugElement {

	static final int prime = 31;
	public static final int r_any = 
			prime * (prime * (prime * IASTNameOwner.r_declaration 
					+ IASTNameOwner.r_definition) + IASTNameOwner.r_reference) + IASTNameOwner.r_unclear;
	
	static final String MAIN_METHOD_NAME = "main";
	
	public static final List<Class<? extends Exception>> DEFAULT_EXCEPTION = Arrays.asList(Exception.class);
	public static final List<Class<? extends Exception>> AST_EXCEPTION = Arrays.asList(ASTException.class);

	@SuppressWarnings("unchecked")
	public static final Class<ASTNode>[] 				AST_NODE = new Class[] {
			ASTNode.class};
	@SuppressWarnings("unchecked")
	public static final Class<Comment>[] 			AST_COMMENT = new Class[] {
			Comment.class};
	@SuppressWarnings("unchecked")
	public static final Class<IASTInitializerClause>[] 	AST_INIT_CLAUSE_TYPE = new Class[] {
			IASTInitializerClause.class};
	@SuppressWarnings("unchecked")
	public static final Class<Expression>[] 		AST_EXPRESSION = new Class[] {
			Expression.class};
	@SuppressWarnings("unchecked")
	public static final Class<Name>[] 		AST_ID_EXPRESSION = new Class[] {
			Name.class};
	@SuppressWarnings("unchecked")
	public static final Class<MethodInvocation>[] AST_FUNCTION_CALL_EXPRESSION = new Class[] {
			MethodInvocation.class};
	@SuppressWarnings("unchecked")
	public static final Class<MethodDeclaration>[] AST_FUNCTION_DEFINITION = new Class[] {
			MethodDeclaration.class};
	@SuppressWarnings("unchecked")
	public static final Class<Statement>[] 			AST_STATEMENT_TYPE = new Class[] {
			Statement.class};
	@SuppressWarnings("unchecked")
	public static final Class<IfStatement>[] 		AST_IF_TYPE = new Class[] {
			IfStatement.class};
	@SuppressWarnings("unchecked")
	public static final Class<ForStatement>[] 		AST_FOR_TYPE = new Class[] {
			ForStatement.class};
	@SuppressWarnings("unchecked")
	public static final Class<Statement>[] 			AST_BRANCH_TYPES = new Class[] {
			SwitchCase.class, DoStatement.class, 
			ForStatement.class, IfStatement.class, WhileStatement.class};
	@SuppressWarnings("unchecked")
	public static final Class<Statement>[] 			AST_LOOP_TYPES = new Class[] {
			DoStatement.class, ForStatement.class, WhileStatement.class};
	@SuppressWarnings("unchecked")
	public static final Class<ArrayAccess>[] 	AST_ARRAY_SUB_TYPE = new Class[] {
			ArrayAccess.class};
	@SuppressWarnings("unchecked")
	public static final Class<ASTNode>[] 				AST_ASSIGNMENT_TYPES = new Class[] {
			IASTUnaryExpression.class, Assignment.class, IASTEqualsInitializer.class};

	
	
	private static ChildListPropertyDescriptor CHILD_LIST_PROPERTY_DESCRIPTOR_CACHE = null;

	private static final Map<IPath, CompilationUnit> 		CU_CACHE = new HashMap<>();
	private static final Map<CompilationUnit, List<Annotation>>	
	PRAGMA_CACHE = new HashMap<>();

	private static final DuoKeyMap<ASTNode, Class<? extends ASTNode>[], List<? extends ASTNode>> 
	ANCESTORS_CACHE = new DuoKeyMap<>();
	private static final DuoKeyMap<ASTNode, Class<? extends ASTNode>, List<? extends ASTNode>> 
	DESCENDANTS_CACHE = new DuoKeyMap<>();

	private static final Map<Name, Name> 					
	AST_NAME_CACHE 			= new HashMap<>();
	private static final DuoKeyMap<IBinding, Integer, Name> 					
	BINDING_NAME_CACHE 			= new DuoKeyMap<>();

	private static final Map<Name, IMethodBinding> 					FUNCTION_CACHE 			= new HashMap<>();
	private static final Map<ASTNode, MethodDeclaration>	WRITING_FUNCTION_CACHE 	= new HashMap<>();
	private static final Map<MethodDeclaration, Boolean> 	GROUND_FUNCTION_CACHE 	= new HashMap<>();
	
	private static final DuoKeyMap<IfStatement, IfStatement, Boolean> 	
	IS_ELSE_TO_CACHE 	= new DuoKeyMap<>();

	// TODO: caching all reusable utility method results

	private static ICProject selectedProj = null;

	private static IIndex index = null;

	
	
	public static IIndex getIndex(boolean refreshesIndex) {
		if (index == null || refreshesIndex)
			try {
				index = CCorePlugin.getIndexManager().getIndex(
						CoreModel.getDefault().getCModel().getCProjects(), 
						IIndexManager.ADD_DEPENDENCIES | IIndexManager.ADD_DEPENDENT);
			} catch (CoreException e) {
				DebugElement.throwTodoException("CDT exception", e);
			}
		return index;
	}

	public static CompilationUnit getAST(IPath cuPath) {
		if (cuPath == null) return null;
		
		// CoreModelUtil.findTranslationUnit(IFile) always return null!
//		CU_CACHE.clear();
		CompilationUnit astCu = CU_CACHE.get(cuPath);
		if (astCu == null) {
		    ASTParser parser = ASTParser.newParser(ASTParser.K_COMPILATION_UNIT);
		    parser.setSource(new String(Files.readAllBytes(cuPath.toPath())).toCharArray());
		    astCu = (CompilationUnit) parser.createAST(null);
		    if (astCu != null) CU_CACHE.put(cuPath, astCu);
		}

		// TODO: automatic refreshing index on index-rebuilt exceptions
//			return tu.getAST(getIndex(refreshesIndex), ITranslationUnit.AST_SKIP_INDEXED_HEADERS);
//		return tu.getAST(
//				getIndex(false), ITranslationUnit.AST_SKIP_INDEXED_HEADERS);
		return astCu;
	}

	public static Collection<CompilationUnit> getRegisteredAST() {
		return CU_CACHE.values();
	}
	

	
	public static List<Annotation> getPragmas(CompilationUnit cu) {
		if (cu == null) return Collections.<Annotation>emptyList();
		
//		PRAGMA_CACHE.clear();
		List<Annotation> ps = PRAGMA_CACHE.get(cu);
		if (ps != null) return ps;
		
		ps = new ArrayList<>();
		for (IASTPreprocessorStatement p : cu.getAllPreprocessorStatements())
			// ps.getParent() returns IASTTranslationUnit
			if (AST_PRAGMA[0].isInstance(p)) ps.add((Annotation) p); 
		PRAGMA_CACHE.put(cu, ps);
		return ps;
	}
	
	/**
	 * @param project
	 */
	public static void setSelectedProject(IProject project) {
		ICProject cProj = CoreModel.getDefault().getCModel().getCProject(project.getName());
		if (cProj == null) throw new IllegalArgumentException("ONLY supporting C/C++ projects!");
		selectedProj = cProj;
	}


	

	/**
	 * @param func
	 * @return
	 */
	public static boolean isMainFunction(MethodDeclaration func) {
		return func.getDeclarator().getName().toString().equals(MAIN_METHOD_NAME);
	}
	
	public static boolean isMainMethod(IMethod method) throws JavaModelException {
	    // Check name
	    if (!MAIN_METHOD_NAME.equals(method.getElementName())) {
	        return false;
	    }
	    
	    // Check static and public
	    int flags = method.getFlags();
	    if (!Flags.isStatic(flags) || !Flags.isPublic(flags)) {
	        return false;
	    }
	    
	    // Check return type is void
	    if (!"V".equals(method.getReturnType())) {
	        return false;
	    }
	    
	    // Check single String array parameter
	    String[] paramTypes = method.getParameterTypes();
	    if (paramTypes.length != 1) {
	        return false;
	    }
	    
	    // Check for String[] - signature is "[QString;"
	    String paramSig = paramTypes[0];
	    return "[QString;".equals(paramSig) || "[Qjava.lang.String;".equals(paramSig);
	}
	
	public static boolean isGround(MethodDeclaration func) {
		if (func == null) return false;
		
		Boolean isGround = GROUND_FUNCTION_CACHE.get(func);
		if (isGround != null) return isGround;
		
		isGround = getFirstDescendantOfAs(func, AST_FUNCTION_CALL_EXPRESSION[0]) == null;
		GROUND_FUNCTION_CACHE.put(func, isGround);
		return isGround;
	}


	
	/**
	 * @param exp
	 * @return true for the null expression.
	 */
	public static boolean isConstant(Expression exp) {
		if (exp == null) return true;
		if (exp instanceof IASTLiteralExpression) return isConstant((IASTLiteralExpression) exp);
		if (exp instanceof IASTUnaryExpression) return isConstant((IASTUnaryExpression) exp);
		if (exp instanceof Assignment) return isConstant((Assignment) exp);
		DebugElement.throwTodoException(toStringOf(exp));
		return false;
	}
	
	public static boolean isConstant(IASTLiteralExpression exp) {
		return true;
	}
	
	public static boolean isConstant(IASTUnaryExpression exp) {
		if (exp == null) return true;
		return isConstant(exp.getOperand());
	}
	
	public static boolean isConstant(Assignment exp) {
		if (exp == null) return true;
		return isConstant(exp.getOperand1()) && isConstant(exp.getOperand2());
	}


	
//	public static boolean isGlobal(Name name) {
//		return name != null && isGlobal(toASTName(name));
//	}
	
	public static boolean isGlobal(Name name) {
		if (name == null) throwNullArgumentException("variable name");
		
		final IBinding bind = getBindingOf(name);
		try {
			return bind.getScope().getKind().equals(EScopeKind.eGlobal);
			
		} catch (DOMException e) {
			return throwASTException(bind, e);
		}
//		IASTTranslationUnit varTu = var.getTranslationUnit();	// needs Name to retrieve its host TU
//		return getAncestorOfAs(varTu.getDeclarationsInAST(var.resolveBinding())[0], IASTDeclarationStatement.class)
//				.getParent() == varTu;
	}

	
	
	/**
	 * @param typeBinding
	 * @return
	 */
	public static boolean isBinary(ITypeBinding typeBinding) {
		if (typeBinding == null) return false;
		if (!typeBinding.isEnum()) return false;
		
		int enumCount = 0;
		for (IVariableBinding varBinding : Arrays.asList(typeBinding.getDeclaredFields())) {
			if (varBinding.isEnumConstant() && typeBinding.equals(varBinding.getType()))
				enumCount++;
			if (enumCount > 2) return false;
		}
		return enumCount == 2;
	}
	
	/**<pre>
	 * Relational expressions exclude shift and equality ones. They are ones with operators >, <, >= and <= ONLY.
	 * 
	 *		relational-op 	One of the following:
	 * 						<
	 * 						<=
	 * 						>
	 * 						>=
	 * <br>
	 *  
	 * @param exp
	 * @return
	 */
	public static boolean isBinaryRelation(Expression exp) {
		if (exp instanceof Assignment) {
			int op = ((Assignment) exp).getOperator();
			return (op == Assignment.op_greaterEqual ||
					op == Assignment.op_greaterThan ||
					op == Assignment.op_lessEqual ||
					op == Assignment.op_lessThan);
		}
		return false;
	}


	
	public static boolean isCollocally(ASTNode node1, ASTNode node2) {
		if (node1 == null || node2 == null) throwNullArgumentException("node");
		return getWritingFunctionDefinitionOf(node1) == getWritingFunctionDefinitionOf(node2);
	}

	public static boolean isParameter(Name id) {
		return id.resolveBinding() instanceof IParameter;
	}
	
	
	
	public static boolean isSameIterationOf(
			final ASTNode node1, final ASTNode node2, final Statement branch) {
		if (node1 == null) throwNullArgumentException("AST node 1");
		if (node2 == null) throwNullArgumentException("AST node 2");
		if (branch == null) throwNullArgumentException("AST branch node");
		
		if (branch instanceof ForStatement) 
			return isSameIterationOf(node1, node2, (ForStatement) branch);
//		else if (branch instanceof WhileStatement) 
//			return branch.contains(node1) && branch.contains(node2);
		else throwTodoException("unsupported branch type");
		
		return false;
	}
	
	private static boolean isSameIterationOf(
			final ASTNode node1, final ASTNode node2, final ForStatement branch) {
		assert node1 != null && node2 != null && branch != null;
		final Statement init = branch.getInitializerStatement();
		final boolean isInit1 = init.contains(node1), isInit2 = init.contains(node2);
		if (isInit1) return isInit2;
		if (isInit2) return isInit1;
		
		final Expression cond = branch.getConditionExpression(), iter = branch.getIterationExpression();
		final boolean isCond1 = cond.contains(node1), isCond2 = cond.contains(node2),
				isIter1 = iter.contains(node1), isIter2 = iter.contains(node2);
		if (isCond1 || isIter1) return isCond2 || isIter2;
		if (isCond2 || isIter2) return isCond1 || isIter1;
		// as usual body containment finally
		return isSameStatementOf(node1, node2, branch.getBody());
	}
	
	private static boolean isSameStatementOf(
			final ASTNode node1, final ASTNode node2, final Statement stat) {
		assert stat != null;
		return stat.contains(node1) && stat.contains(node2);
	}
	
	public static boolean isSameBranchOf(
			final ASTNode node1, final ASTNode node2, final Statement branch) {
		if (node1 == null) throwNullArgumentException("AST node 1");
		if (node2 == null) throwNullArgumentException("AST node 2");
		if (branch == null) throwNullArgumentException("AST branch node");
		
		if (branch instanceof IfStatement) return isSameBranchOf(node1, node2, (IfStatement) branch);
		
//		Statement body = null;
//		if (branch instanceof ForStatement) body = ((ForStatement) branch).getBody();
//		else if (branch instanceof WhileStatement) body = ((WhileStatement) branch).getBody();
//		else throwTodoException("unsupported branch type");
		
		return branch.contains(node1) && branch.contains(node2);
	}
	
	private static boolean isSameBranchOf(
			final ASTNode node1, final ASTNode node2, final IfStatement branch) {
		assert node1 != null && node2 != null && branch != null;
		final Statement then = branch.getThenClause(), els = branch.getElseClause();
		return (then != null && then.contains(node1) && then.contains(node2)) 
				|| (els != null && els.contains(node1) && els.contains(node2)); 
	}
	
	/**
	 * @param node1
	 * @param node2
	 * @param branch
	 * @return true when there's 1) extra-if mutex branch or 2) intra-if mutex branch
	 */
	public static boolean isMutexBranchOf(
			final ASTNode node1, final ASTNode node2, final IfStatement branch) {
		if (node1 == null) throwNullArgumentException("AST node 1");
		if (node2 == null) throwNullArgumentException("AST node 2");
		if (branch == null) throwNullArgumentException("AST branch node");

		final Statement then = branch.getThenClause();
		if (then == null) return false;

		final boolean thenc1 = then.contains(node1), thenc2 = then.contains(node2);
		if (thenc1 && thenc2) return false;
		
		final Statement els = branch.getElseClause();
		final boolean ie = els != null, elsec1 = ie && els.contains(node1), elsec2 = ie && els.contains(node2);
		if (elsec1 && elsec2) return false; 

		// !thenc2 && (elsec2:intra-if || !elsec2:extra-if)
		// !thenc1 && (elsec1:intra-if || !elsec1:extra-if)
		if (thenc1 || thenc2) return true;	
		
		// !thenc1 && !thenc2 && extra-if
		return !(!elsec1 && !elsec2); 
	}

	public static boolean isElse(Statement stat) {
		if (stat == null) return false;
		
		IfStatement parIf = getAncestorOfAs(stat, AST_IF_TYPE, true);
		if (parIf == null) return false;
		
		return parIf.getElseClause() == stat;
	}
	
	public static boolean isElseOf(final ASTNode node, final IfStatement ifStat) {
		if (node == null || ifStat == null) return false;
		
		final Statement parent = getAncestorOfAs(node, AST_STATEMENT_TYPE, true);
		if (parent == null) return false;
		if (parent == ifStat.getElseClause()) return true;
		return isElseOf(parent.getParent(), ifStat);
	}
	
	public static boolean isElseTo(ASTNode node1, ASTNode node2) {
		final IfStatement if1 = getAncestorOfAs(node1, AST_IF_TYPE, true),
				if2 = getAncestorOfAs(node2, AST_IF_TYPE, true);
		return if1 == if2 ? isElseOf(node1, if1) : isElseTo(if1, if2);
	}
	
//	public static boolean isElseTo(Statement stat1, Statement stat2) {
//		return isElseTo(stat1 instanceof IfStatement ? 
//				(IfStatement) stat1 : getAncestorOfAs(stat1, AST_IF_TYPE, false), 
//				stat2 instanceof IfStatement ? 
//				(IfStatement) stat2 : getAncestorOfAs(stat2, AST_IF_TYPE, false));
//	}
	
	public static boolean isElseTo(IfStatement if1, IfStatement if2) {
		if (if1 == null || if2 == null) return false;
		if (if1 == if2) return false;
		
		Boolean isET = IS_ELSE_TO_CACHE.get(if1, if2);
		if (isET == null) { 
			if (if1.contains(if2)) isET = containsElseTo(if1, if2);
			else if (if2.contains(if1)) isET = containsElseTo(if2, if1);
			else isET = false;

//			// Ancestor {@code if2} traversal first, then descendant {@code if2} traversal.
//			// Ancestor if2 traversal
//			if (isElseTo(if1, getAncestorOfAs(if2, AST_IF_TYPE, false))) {
//				isET = true; break computeIsET;}
//			
//			// descendant if2 traversal - avoiding if2d -> if2d's ancestor -> if2d ...
			
			IS_ELSE_TO_CACHE.put(if1, if2, isET);
		}
		return isET;
	}
	
	private static boolean containsElseTo(IfStatement if1, IfStatement if2) {
		assert if1 != null && if2 != null && if1.contains(if2);
		final Statement if1else = if1.getElseClause();
		if (if1else == null) return false;
		if (if1else == if2) return true;
		
		for (IfStatement if1d : getDescendantsOfAs(if1else, AST_IF_TYPE[0]))
			if (if1d == if2) return true; 
		return false;
	}
	
	
	
	public static boolean dependsOn(MethodDeclaration f1, MethodDeclaration f2) {
		if (f1 == null || f2 == null) return false;
		if (isGround(f1)) return false;
		
		final Name f2n = getNameOf(f2);
		for (MethodInvocation call : 
			getDescendantsOfAs(f1, AST_FUNCTION_CALL_EXPRESSION[0])) 
			if (equals(f2n, getEnclosingFunctionCallNameOf(call))) return true;
		return false;
	}
	
	public static boolean dependsOnElseTo(ASTNode node1, ASTNode node2) {
		return isElseTo(node1, node2);
		
//		final IfStatement if1 = getAncestorOfAs(node1, AST_IF_TYPE, true),
//				if2 = getAncestorOfAs(node2, AST_IF_TYPE, true);
//		return if1 == if2 ? isElseOf(node1, if1) : isElseTo(if1, if2);
	}
	

	
	/**
	 * @param descend
	 * @param stopTypes - the inclusive stop types during traversing 
	 * ancestors
	 * @return A descendant-inclusive ancestor list.
	 */
	@SuppressWarnings("unchecked")
	public static <StopAncestor extends ASTNode> List<ASTNode> 
	getAncestorsOfUntil(ASTNode descend, Class<StopAncestor>[] stopTypes) {
		if (descend == null) return null;
//		if (descend == null) return throwNullArgumentException("descendant node");
		
		List<ASTNode> ancestors = 
				(List<ASTNode>) ANCESTORS_CACHE.get(descend, stopTypes);
		
		if (ancestors == null) {
			traverseAncestors: {
			if (stopTypes != null) 
				for (Class<StopAncestor> stopType : stopTypes) 
					if (stopType.isInstance(descend)) 
						break traverseAncestors;
			
			ancestors = getAncestorsOfUntil(getParentOf(descend), stopTypes);
			}

			ancestors = ancestors == null 
					? new ArrayList<ASTNode>() 
					: new ArrayList<ASTNode>(ancestors);
			ancestors.add(0, (StopAncestor) descend);
			ANCESTORS_CACHE.put(descend, stopTypes, ancestors);
		}
		
		return ancestors;
	}

	/**
	 * @param descend
	 * @param ancestorTypes
	 * @return the closest ancestor of descend (either inclusively or 
	 * exclusively) 
	 * 	in one of ancestorTypes. 
	 */
	public static <Ancestor extends ASTNode> Ancestor getAncestorOfAs(
			ASTNode descend, Class<Ancestor>[] ancestorTypes, Boolean includesDescend) {
		return getAncestorOfAsUnless(
				descend, ancestorTypes, null, includesDescend);
	}
	
	/**
	 * @param descend
	 * @param ancestorTypes
	 * @param stopTypes
	 * @param includesDescend
	 * @return the closest ancestor of descend (exclusively) in one of ancestorTypes. 
	 */
	@SuppressWarnings("unchecked")
	public static <Ancestor extends ASTNode, StopAncestor extends ASTNode> 
	Ancestor getAncestorOfAsUnless(ASTNode descend, Class<Ancestor>[] ancestorTypes,
			Class<StopAncestor>[] stopTypes, Boolean includesDescend) {
		if (descend == null || ancestorTypes == null) 
			return null;
//			return throwNullArgumentException("descendant node");

		if (includesDescend == null) {
			Class<?> dc = descend.getClass();
			for (Class<?> ac : ancestorTypes) try {
				includesDescend = dc.asSubclass(ac) != null;
			} catch (ClassCastException e) {
				includesDescend = false;
			}
		}
		List<ASTNode> ans = getAncestorsOfUntil(descend, stopTypes);	// inclusive ancestors
		for (ASTNode a : ans.subList(includesDescend ? 0 : 1, ans.size())) 
			for (Class<Ancestor> at : ancestorTypes) 
				if (at.isInstance(a)) return (Ancestor) a;
		
		return null;
		
//		traverseParents: {	
//			ASTNode ancestor = descend.getParent();
//			while (ancestor != null) {
//				if (ancestorTypes != null) 
//					for (Class<Ancestor> ancestorType : ancestorTypes) 
//						if (ancestorType.isInstance(ancestor)) 
//							break traverseParents;
//				if (stopTypes != null) 
//					for (Class<? extends ASTNode> stopType : stopTypes) 
//						if (stopType.isInstance(ancestor)) 
//							return null;
//				ancestor = ancestor.getParent();
//			}
//		}
//		return (Ancestor) ancestor;
	}
	
	public static IASTInitializerClause getAncestorClauseOf(
			final ASTNode descend, final boolean includesDescend) {
		return getAncestorOfAs(descend, ASTUtil.AST_INIT_CLAUSE_TYPE, includesDescend);
	}
			
	public static <Ancestor extends ASTNode> int getContinuousAncestorsCountOf(
			ASTNode descend, Class<Ancestor> ancestorType) {
		int count = 0;	// TODO: caching count
		boolean isContinuous = true;
		ASTNode ancestor = descend;
		
		while (ancestor != null && isContinuous) 	// descend may be null
			if (ancestorType.isInstance(ancestor)) {
				count++;
				ancestor = getParentOf(ancestor);
			} else isContinuous = false;
		
		return count;
	}

	public static List<ASTNode> getChildrenOf(ASTNode parent) {
		if (parent != null) {
			if (CHILD_LIST_PROPERTY_DESCRIPTOR_CACHE == null) 
				for (StructuralPropertyDescriptor spd : parent.structuralPropertiesForType())
					if (spd.isChildListProperty()) {
						CHILD_LIST_PROPERTY_DESCRIPTOR_CACHE = (ChildListPropertyDescriptor) spd;
						break;
					}
			return parent.getStructuralProperty(CHILD_LIST_PROPERTY_DESCRIPTOR_CACHE);
		}
		return Collections.emptyList();
	}
	
	@SuppressWarnings("unchecked")
	public static <Descendant extends ASTNode> Iterable<Descendant> getDescendantsOfAs(
			ASTNode ancestor, Class<Descendant> descendType) {
		if (ancestor == null) return null;
		
		List<Descendant> descendants = 
				(List<Descendant>) DESCENDANTS_CACHE.get(ancestor, descendType);
		if (descendants != null) return descendants;
		
		descendants = new ArrayList<Descendant>();
		for (ASTNode child : ancestor.getChildren()) if (child != null) {
			if (descendType.isInstance(child)) descendants.add((Descendant) child);
			descendants.addAll(
					(Collection<? extends Descendant>) getDescendantsOfAs(child, descendType));
		}
		DESCENDANTS_CACHE.put(ancestor, descendType, descendants);
		return descendants;
	}
	
	@SuppressWarnings("unchecked")
	public static <Descendant extends ASTNode> Descendant getFirstDescendantOfAs(
			ASTNode ancestor, Class<Descendant> descendType) {
		// TODO: caching the first descendant
		if (ancestor == null) return null;
		
		for (ASTNode child : ancestor.getChildren())
			if (child != null)
				if (descendType.isInstance(child)) return (Descendant) child;
				else {
					Descendant descend = getFirstDescendantOfAs(child, descendType);
					if (descend != null) return descend;
				}
		
		return null;
	}
	
	public static ASTNode getLastDescendantOf(ASTNode ancestor) {
		// TODO: caching the last descendant
		if (ancestor == null) return null;
		
		final ASTNode[] children = ancestor.getChildren();
		if (children == null) return ancestor;
		final int childSize = children.length;
		if (childSize <= 0) return ancestor;
		return getLastDescendantOf(children[childSize - 1]);
	}
	
	
	
	public static ASTNode getParentOf(final ASTNode descend) {
		if (descend == null) throwNullArgumentException("descendant");
		return descend instanceof Annotation
				? getParentOf((Annotation) descend)
				: descend.getParent();
	}
	
	public static ASTNode getParentOf(final Annotation descend) {
		if (descend == null) throwNullArgumentException("descendant");
		
		final IASTFileLocation l = descend.getFileLocation();
		return descend.getTranslationUnit().getNodeSelector(null).findEnclosingNode(
				l.getNodeOffset() - 1, l.getNodeLength() + 1);
	}
	
	public static Statement getParentBranchOf(ASTNode descend) {
		return getAncestorOfAs(descend, ASTUtil.AST_BRANCH_TYPES, false);
	}
	
//	/**
//	 * @param me
//	 * @param start
//	 * @param length
//	 * @param tu
//	 * @param ns
//	 * @return the direct biggest small sibling node of {@code me} in AST.
//	 */
//	private static ASTNode previousOfContained(final ASTNode me, 
//			final int[] start, final int[] length, 
////			final boolean includesPragma, 
//			final IASTTranslationUnit tu, final IASTNodeSelector ns) {
//		assert me != null && start != null && start.length > 0 
//				&& length != null && length.length > 0 && tu != null && ns != null;
//		
//		ASTNode pre = null;
//		while (start[0] > 0) {
//			// TODO: binary search: start[0]-=2n, length[0]+=2n
//			pre = ns.findFirstContainedNode(start[0]--, length[0]++);
//			if (pre != null) break;
//		}
//
////		if (includesPragma) pre = previousPragmaOfAfter(me, pre, tu);
//		return pre;
//	}
	

	
	public static Iterable<Name> getIdsUsedBy(Expression exp) {
		return getDescendantsOfAs(exp, Name.class);
	}

	/**
	 * TODO: caching count?
	 * 
	 * @param name
	 * @param root
	 * @return
	 */
	public static int countNamesOfIn(Name name, ASTNode root) {
		if (name == null || root == null) return 0;
		
		final ASTNameCollector nc = new ASTNameCollector(name.getFullyQualifiedName());
		root.accept(nc);
		return nc.getNames().size();
	}
	
	public static <Descendant extends ASTNode> int countDirectContinuousDescendantsOf(
			ASTNode ancestor, Class<Descendant> descendType) {
		if (ancestor == null) return 0;
		
		int count = 0;	// TODO: caching count
		for (ASTNode child : ancestor.getChildren())
			if (child != null && descendType.isInstance(child))
				count += (1 + countDirectContinuousDescendantsOf(child, descendType));
		
		return count;
	}
	
	public static List<MethodDeclaration> findAllMainMethods(IJavaProject project) 
	        throws JavaModelException {
	    List<MethodDeclaration> mainMethods = new ArrayList<>();
	    
	    // Search all packages
	    for (IPackageFragment pkg : project.getPackageFragments()) {
	        if (pkg.getKind() == IPackageFragmentRoot.K_SOURCE) {
	            for (ICompilationUnit cu : pkg.getCompilationUnits()) {
	                for (org.eclipse.jdt.core.IType type : cu.getAllTypes()) {
	                    for (IMethod method : type.getMethods()) {
	                        if (isMainMethod(method)) {
	                            MethodDeclaration decl = getMethodDeclarationFromIMethod(method);
	                            if (decl != null) {
	                                mainMethods.add(decl);
	                            }
	                        }
	                    }
	                }
	            }
	        }
	    }
	    
	    return mainMethods;
	}
	
	/**
	 * @param descend
	 * @param ancestor - a descendant-inclusive ancestor
	 * @param ancestors - a pre-cached ancestor list if available
	 * @return
	 */
	public static boolean hasAncestorAs(
			ASTNode descend, ASTNode ancestor, List<ASTNode> ancestors) {
		if (descend == null || ancestor == null) return false;
		if (descend == ancestor) return true;	// excluding the null case above
		
		int ancestorsSize;
		// case of descend == ancestors[0] == ancestor
		if (ancestors != null && descend == ancestors.get(0)) {
			ancestorsSize = ancestors.size();
			if (ancestorsSize > 1)
				for (ASTNode anc : ancestors.subList(1, ancestorsSize)) 
					if (anc == ancestor) return true; 
		}

		// resolving ancestors if no valid cache available
		ancestors = getAncestorsOfUntil(descend, null);
		
		// excluding the already handled case of descend == ancestors[0] == ancestor
		if (ancestors != null) {
			ancestorsSize = ancestors.size();
			if (ancestorsSize > 1) 
				for (ASTNode anc : ancestors.subList(1, ancestorsSize)) 
					if (anc == ancestor) return true; 
		}
		return false;
	}
	


	
	
	
	
//	public static int getDeclaredDim(ArrayAccess array) {
//		findDeclaration(((Name) array.getArrayExpression()).getName());
//		return 0;
//	}
	
	
	
	public static Name getDefinitionOf(Name name) {
		if (name == null) return null;
		
		// Searching for local definition first
		Name[] defs = 
				name.getTranslationUnit().getDefinitions(name.resolveBinding());
		if (defs != null && defs.length > 0) return defs[0];
		
		// Searching for global definition
		IIndex index = getIndex(false);
		try {
			index.acquireReadLock();
			// IIndex doesn't find names for IParameter's
//			defs = index.findNames(
//					name.resolveBinding(), IIndex.FIND_ALL_OCCURRENCES);	// internal NullPointerException!
			for (IIndexBinding bind : index.findBindings(
					name.toCharArray(), IndexFilter.ALL, new NullProgressMonitor())) {
				defs = index.findReferences(bind);
				if (defs != null && defs.length > 0) return defs[0];
			}
		} catch (InterruptedException | CoreException e) {
			DebugElement.throwTodoException(e.toString());
		} finally {
			index.releaseReadLock();
		}
		return null;
	}
	
	public static MethodDeclaration getDefinitionOf(IMethodBinding f) {
		if (f == null) DebugElement.throwNullArgumentException("function");

		for (Name n : getNameOf(f)) {
			final MethodDeclaration d = getWritingFunctionDefinitionOf(n);
			// excluding function calls
//			if (d != null && getNameOf(d).resolveBinding().equals(f)) 
			if (d != null && Elemental.tests(()->
			getNameOf(d).resolveBinding().toString().equals(f.toString()))) 
				return d;	
		}
		return null;
//		return getWritingFunctionDefinitionOf(getNameOf(f, IASTNameOwner.r_definition));
	}
	
	public static IBinding getBindingOf(Name name) {
		if (name == null) throwNullArgumentException("name");
		
		return name.resolveBinding();

//		IIndex index = getIndex(false);
//		// read-lock pattern on the IIndex
//		try {
//			index.acquireReadLock();
//			bind = index.findBinding(name);
//		} catch (CoreException | InterruptedException e) {
//			throwTodoException(e);
//		} finally {
//			index.releaseReadLock();
//		}
//		return bind;
	}
	
//	@SuppressWarnings("unchecked")
//	public static <T extends ASTNode> T getFrozenOriginalNodeOf(T copy) {
//		if (copy == null) return copy;
//		
//		final T ori = (T) copy.getOriginalNode();
//		if (copy.isFrozen()) return ori;
//		
//		// non-frozen copy
//		final ASTNode oriParent = getFrozenOriginalNodeOf(copy.getParent());
//		if (oriParent == null) return ori;
//		for (ASTNode child : oriParent.getChildren()) {
//			if (child.equals(copy)) return (T) child.getOriginalNode();
//		}
//		return DebugElement.throwTodoException("unsupported copy");
//	}
	
	public static MethodDeclaration getMethodDeclarationFromIMethod(IMethod method) 
	        throws JavaModelException {
	    ICompilationUnit icu = method.getCompilationUnit();
	    if (icu == null) {
	        return null;
	    }
	    
	    // Parse the compilation unit to get AST
	    ASTParser parser = ASTParser.newParser(AST.JLS_Latest);
	    parser.setSource(icu);
	    parser.setResolveBindings(true);
	    parser.setKind(ASTParser.K_COMPILATION_UNIT);
	    
	    CompilationUnit cu = (CompilationUnit) parser.createAST(null);
	    
	    // Find the method in the AST
	    IMethod targetMethod = method;
	    final MethodDeclaration[] result = new MethodDeclaration[1];
	    
	    cu.accept(new ASTVisitor() {
	        @Override
	        public boolean visit(MethodDeclaration node) {
	            IMethodBinding binding = node.resolveBinding();
	            if (binding != null) {
	                IMethod iMethod = (IMethod) binding.getJavaElement();
	                if (iMethod != null && iMethod.equals(targetMethod)) {
	                    result[0] = node;
	                    return false;
	                }
	            }
	            return true;
	        }
	    });
	    
	    return result[0];
	}
	
	/**
	 * @param fName - the name of function to search for
	 * @return
	 */
	public static IMethodBinding getMethodBindingOf(Name fName) {
		if (fName == null) return null;
		
		IBinding fBind = getBindingOf(fName);
		if (fBind instanceof IMethodBinding) return (IMethodBinding) fBind;
		
//		f = fbind.getAdapter(IMethodBinding.class);	// IIndexBinding has NO adapters for IMethodBinding!
		IMethodBinding f = FUNCTION_CACHE.get(fName);
		if (f == null) {
			final Name fASTName = toASTName(fName);
			if (fASTName != null) {
				fBind = fASTName.resolveBinding();
				if (fBind instanceof IMethodBinding) FUNCTION_CACHE.put(fName, f = (IMethodBinding)fBind); 
			}
		}
		return f;
	}

	public static MethodDeclaration getWritingFunctionDefinitionOf(ASTNode node) {
		if (node == null) throwNullArgumentException("node");
		if (node instanceof MethodDeclaration) return (MethodDeclaration) node;
		
		MethodDeclaration def = WRITING_FUNCTION_CACHE.get(node);
		if (def == null) WRITING_FUNCTION_CACHE.put(
				node, 
				def = (MethodDeclaration) getAncestorOfAs(
						node, AST_FUNCTION_DEFINITION, false));
		return def;
	}

	
	
	public static MethodInvocation getEnclosingFunctionCallOf(ASTNode node) {
		return getAncestorOfAsUnless(
				node, AST_FUNCTION_CALL_EXPRESSION, AST_STATEMENT_TYPE, true);
	}
	
	public static Name getEnclosingFunctionCallNameOf(MethodInvocation call) {
		if (call == null) throwNullArgumentException("call");
		
		Expression callNameExp = call.getFunctionNameExpression();
		if (callNameExp instanceof Name) 
			return ((Name) callNameExp).getName();
		// TODO: else if ...
		return null;
	}
	
	public static Name getEnclosingFunctionCallNameOf(ASTNode node) {
		// call != null -> call instanceof MethodInvocation
		return getEnclosingFunctionCallNameOf(getEnclosingFunctionCallOf(node));
	}
	
	

	/**<pre>
	 * Retrieving the direct parent loop within the same function definition.
	 * </pre>
	 * 
	 * @param node
	 * @return
	 */
	public static ForStatement getEnclosingForOf(ASTNode node) {
		return getAncestorOfAsUnless(
				node, 
				AST_FOR_TYPE,
				AST_FUNCTION_DEFINITION, 
				false);
	}
	
	/**<pre>
	 * Retrieving the direct parent loop within the same function definition.
	 * 
	 * Only supporting the OpenMP canonical for-loop 
	 * ({@linkplain OpenMP ﻿http://www.openmp.org/mp-documents/openmp-4.5.pdf}).
	 * 
	 * TODO: getEnclosingLoopCondition(...) for handling break/continue statements and while-loop conditions.
	 * <br>
	 * 
	 * @param innerLoop
	 * @return
	 */
	public static ForStatement getEnclosingForOf(final ForStatement innerLoop) {
		return getAncestorOfAsUnless(
				innerLoop, 
				AST_FOR_TYPE,
				AST_FUNCTION_DEFINITION, 
				false);
	}
	
//	/**
//	 * @param conditionalStatement - supposed to be a conditional (branching) statement, 
//	 * 	which is one of {@link SwitchCase}, {@link DoStatement}, {@link ForStatement}, {@link IfStatement} and 
//	 * 	{@link WhileStatement} 
//	 * @return
//	 */
//	public static Expression getConditionExpressionOf(Statement conditionalStatement) {
//		if (conditionalStatement == null) return null;
//		
//		if (conditionalStatement instanceof SwitchCase)
//			return ((SwitchCase) conditionalStatement).getExpression();
//		if (conditionalStatement instanceof DoStatement)
//			return ((DoStatement) conditionalStatement).getExpression();
//		if (conditionalStatement instanceof ForStatement)
//			return ((ForStatement) conditionalStatement).getExpression();
//		if (conditionalStatement instanceof IfStatement)
//			return ((IfStatement) conditionalStatement).getExpression();
//		if (conditionalStatement instanceof WhileStatement)
//			return ((WhileStatement) conditionalStatement).getExpression();
//		return null;
//	}
	


	public static IfStatement getEnclosingIfStatementOf(ASTNode node) {
		if (node == null) DebugElement.throwNullArgumentException("AST node");
		return (IfStatement) getAncestorOfAs(
				node, AST_IF_TYPE, true);
	}
	
	@SuppressWarnings("unchecked")
	public static IASTSwitchStatement getEnclosingSwitchStatementOf(Statement stat) {
		if (stat == null) DebugElement.throwNullArgumentException("AST statement");
		return (IASTSwitchStatement) getAncestorOfAs(
				stat, new Class[] {IASTSwitchStatement.class}, true);
	}
	

	
	public static ArrayAccess getEnclosingArraySubscriptOf(
			final ASTNode node) {
		return getAncestorOfAsUnless(
				node, 
				AST_ARRAY_SUB_TYPE,
				AST_STATEMENT_TYPE, 
				true);
	}
	
	/**
	 * @param node
	 * @return @NotNull list.
	 */
	public static List<ArrayAccess> getEnclosingArraySubscriptsOf(final ASTNode node) {
		final List<ArrayAccess> enclosings = new ArrayList<>();
		final List<ASTNode> ancs = getAncestorsOfUntil(node, AST_STATEMENT_TYPE);
		for (ASTNode anc : ancs) 
			if (anc instanceof ArrayAccess) enclosings.add((ArrayAccess) anc);
		return enclosings;
	}
	
	
	
	@SuppressWarnings("unchecked")
	public static ReturnStatement getEnclosingReturnStatementOf(ASTNode node) {
		if (node == null) DebugElement.throwNullArgumentException("AST node");
		return (ReturnStatement) getAncestorOfAs(
				node, new Class[] {ReturnStatement.class}, true);
	}
	
	public static List<ReturnStatement> getReturnStatementsOf(ASTNode node) {
		return new ASTReturnVisitor().findIn(node);
	}
	
	public static ReturnStatement nextReturnStatementTo(ASTNode node) {
		return new ASTReturnVisitor().findNextTo(node);
	}
	
	private static class ASTReturnVisitor extends GenericAstVisitor {
		private boolean hasFoundNode = false;
		private boolean findsIn = false;
		private boolean findsNextTo = false;
		private ASTNode n = null;
		final private List<ReturnStatement> rs = new ArrayList<>();
		
		public ASTReturnVisitor() {
			super(true);
			shouldVisitStatements = true;
		}

		public List<ReturnStatement> findIn(ASTNode node) {
			if (node == null) DebugElement.throwNullArgumentException("AST node");
			
			final MethodDeclaration f = getWritingFunctionDefinitionOf(node);
			if (f == null) DebugElement.throwNullArgumentException("function child");
			findsIn = true; n = node;
			f.accept(this);
			return rs;
		}
		
		public ReturnStatement findNextTo(ASTNode node) {
			if (node == null) DebugElement.throwNullArgumentException("AST node");
			
			final MethodDeclaration f = getWritingFunctionDefinitionOf(node);
			if (f == null) return null;		// node is global
			
			findsNextTo = true; n = node;
			f.accept(this);
			return rs.isEmpty() ? null : rs.get(0);
		}
		
		@Override
		protected int genericVisit(ASTNode node) {
			if (node == n) hasFoundNode = true;
			return PROCESS_CONTINUE;	// continue-ing to find r
		}
		
		@Override
		protected int genericLeave(ASTNode node) {
			if (findsIn && node == n) return PROCESS_ABORT;
			return PROCESS_CONTINUE;	// continue-ing to find r if findsNextTo
		}

		@Override
		public int visit(Statement statement) {
			if (statement instanceof ReturnStatement && hasFoundNode) {
				rs.add((ReturnStatement) statement);
				if (findsNextTo) return PROCESS_ABORT;
			} 
			return PROCESS_CONTINUE;	// continue-ing to find n
		}
	}
	
	
	
	/**
	 * @param exp
	 * @return
	 */
	public static Expression unbracket(IASTUnaryExpression exp) {
		// TODO: caching results
		Expression ubExp = exp;
		if (exp.getOperator() == IASTUnaryExpression.op_bracketedPrimary) {
			ubExp = exp.getOperand();
			if (ubExp instanceof IASTUnaryExpression) return unbracket((IASTUnaryExpression) ubExp);
		}
		return ubExp;
	}
	
	
	
	public static Name getNameFrom(IPath tuPath, int offset, int length, boolean refreshesIndex) {
		IASTTranslationUnit ast = getAST(tuPath, refreshesIndex);
		if (ast == null) return null;
		else return ast.getNodeSelector(null).findFirstContainedName(offset, length);
//		else return ast.getNodeSelector(tuPath.toString()).findFirstContainedName(offset, length);
	}

	public static Name getNameFrom(IASTFileLocation loc, boolean refreshesIndex) {
		return getNameFrom(
				new Path(loc.getFileName()), 
				loc.getNodeOffset(), loc.getNodeLength(), refreshesIndex);
	}
	
	public static Name getNameOf(final IASTNameOwner owner) {
		if (owner == null) return null;
		
		for (ASTNode child : ((ASTNode)owner).getChildren()) 
			if (child instanceof Name) return (Name) child;
		return null;
	}
	
	/**
	 * @param exp
	 * @return
	 */
	public static Name getNameOf(final Name exp) {
		return (exp != null) ? exp.getName() : null;
	}
	
	public static Name getNameOf(MethodInvocation exp) {
		return exp != null 
				? getNameOf(exp.getFunctionNameExpression()) : null;
	}

	/**
	 * @param exp
	 * @return
	 */
	public static Name getNameOf(final Expression exp) {
		if (exp instanceof Name) 
			return getNameOf((Name) exp);
		
		else if (exp instanceof MethodInvocation) 
			return getNameOf((MethodInvocation) exp);
		
		else if (exp instanceof IASTUnaryExpression) 
			return getNameOf(((IASTUnaryExpression) exp).getOperand());
		
		return DebugElement.throwTodoException("unsupported expression");
	}

	public static Name getNameOf(MethodDeclaration f) {
		if (f == null) return null;
		else return f.getDeclarator().getName();
	}
	
	/**
	 * @param bind - not for IParameter's since IIndex finds NO them
	 * @param role TODO
	 * @return
	 */
	public static Name getNameOf(IBinding bind, int role) throws ASTException {
		if (bind == null) DebugElement.throwNullArgumentException("binding");
		
		Name astName = BINDING_NAME_CACHE.get(bind, role);
		if (astName != null) return astName;
		
//		final boolean hasRole = role != r_any;
		int iRole;
		switch (role) {
		case IASTNameOwner.r_declaration:	iRole = IIndex.FIND_DECLARATIONS;		break;
		case IASTNameOwner.r_definition:	iRole = IIndex.FIND_DEFINITIONS;		break;
		case IASTNameOwner.r_reference:		iRole = IIndex.FIND_REFERENCES;			break;
		case IASTNameOwner.r_unclear:		iRole = IIndex.FIND_POTENTIAL_MATCHES;	break;
		case r_any:
		default:							iRole = IIndex.FIND_ALL_OCCURRENCES;
		}
		
		IIndex index = getIndex(false);
		try {
			index.acquireReadLock();
			
			// IIndex doesn't find names for IParameter's
			Name[] bindNames = index.findNames(bind, iRole);
			if (bindNames != null) for (Name name : bindNames) {
				astName = toASTName(name);
				if (astName != null) {
					assert astName.resolveBinding().equals(bind); break;
//					if (!hasRole || role == astName.getRoleOfName(true)) break;
				}
			}
			
		} catch (Exception e) {
			throwASTException(bind, e);
		} finally {
			index.releaseReadLock();
		}
		BINDING_NAME_CACHE.put(bind, role, astName);
		return astName;
	}
	
	public static Collection<Name> getNameOf(IBinding bind) {
		try {
			final Set<Name> names = new HashSet<>();
			Elemental.add(names, ()-> getNameOf(bind, IASTNameOwner.r_definition), AST_EXCEPTION);
			if (names.isEmpty()) Elemental.add(names, ()-> getNameOf(bind, IASTNameOwner.r_declaration), AST_EXCEPTION);
			if (names.isEmpty()) Elemental.add(names, ()-> getNameOf(bind, ASTUtil.r_any), AST_EXCEPTION);
			if (names.isEmpty()) {
				final ASTNameCollector nc = new ASTNameCollector(bind.getName());
				for (IASTTranslationUnit ast : getRegisteredAST()) {
					if (!ast.accept(nc)) DebugElement.throwTodoException("failed AST visiting");
					names.addAll(Elemental.toList(nc.getNames())); 
//					for (Name n : Elemental.toList(nc.getNames())) 
//						Elemental.addSkipNull(names, ()-> n, ()-> n.resolveBinding().equals(bind), AST_EXCEPTION);
				}
			}
			return names;
			
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
	public static Collection<Name> getNameOf(IMethodBinding func) {
		if (func == null) DebugElement.throwNullArgumentException("function");
		
		final Set<Name> names = new HashSet<>();
		final Collection<Entry<Name,IMethodBinding>> funcs = FUNCTION_CACHE.entrySet();
		for (Entry<Name,IMethodBinding> f : funcs) if (f.getValue().equals(func)) {
			final Name fn = f.getKey();
			if (fn instanceof Name) names.add((Name) fn);  
		}
		names.addAll(getNameOf((IBinding) func));
		return names;
	}
	
	/**
	 * @param bind - not for IParameter's since IIndex finds NO them
	 * @param scope - pre-cached scope name since both IBinding.getScope().getScopeName() and 
	 * 				IMethodBinding.getFunctionScope().getScopeName() returns null!
	 * @return
	 */
	public static Name getNameOfFrom(IBinding bind, Name scope) {
		if (bind == null) DebugElement.throwNullArgumentException("binding");
		
		MethodDeclaration scopeAST = 
				getWritingFunctionDefinitionOf(toASTName(scope));
		if (scopeAST != null) 
			for (Name descendName : getDescendantsOfAs(scopeAST, Name.class)) 
				if (descendName.resolveBinding().equals(bind)) return descendName;
		
		return getNameOf(bind, r_any);
	}

	public static int getStartingLineNumberOf(ASTNode node) {
        if (node == null) return SystemElement.throwNullArgumentException("node");
	    return ((CompilationUnit) node.getRoot()).getLineNumber(node.getStartPosition());
	}
	
//	public static Name toASTName(Name Name) {
//		if (Name == null) return null;
//		
//		if (Name instanceof Name) return (Name) Name;
//		else {
////			return getNameFrom(Name.getFileLocation(), false);
//			Name aName = AST_NAME_CACHE.get(Name);
//			if (aName == null) AST_NAME_CACHE.put(
//					Name, aName = getNameFrom(Name.getFileLocation(), false));
//			return aName;
//		}
//	}
	
	/**
	 * @param name
	 * @return
	 */
	public static String toStringOf(Name name) {
		if (name == null) return null;
		return name.toString() + " " + toStringOf(name.getNodeLocations());
//		return name.toString() + "\n" + toStringOf(name.getFileLocation()) + "\n";
	}

	public static String toStringOf(ASTNode... nodes) {
		if (nodes == null) DebugElement.throwNullArgumentException("location");
		
		String str = "";
		for (ASTNode node : nodes) 
			str += ((node instanceof IASTFileLocation 
					? toStringOf((IASTFileLocation) node)
					: node.toString()) + "\n");
		return str;
	}
	
//	public static String toStringOf(IASTMacroExpansionLocation location) {
//		if (location == null) DebugElement.throwNullArgumentException("location");
//		return location.toString();
//	}
	
//	public static String toStringOf(IASTFileLocation location) {
//		if (location == null) return "(null)";
//		
//		String fName = location.getFileName(), 
//				fnFolders[] = fName.split("/");
//		fName = "";
//		for (String fd : fnFolders) 
//			fName = fd + (fName.isEmpty() ? "" : (" @ " + fName));
//		return "at line " + location.getStartingLineNumber() + 
//				" (~" + location.getNodeOffset() + 
//				")\nof file " + fName;
//	}
	
	public static String toStringOf(ASTNode node) {
	    if (node == null) return SystemElement.throwNullArgumentException("node");
		
		if (node instanceof Expression) return ((Expression)node).toString();
				
		for (ASTNode child : node.getChildren()) {
			if (child instanceof Name) return toStringOf((Name) child);
			else return toStringOf(child.getFileLocation());
		}
		return toStringOf(node.getFileLocation());
	}
	
	public static String toLocationOf(ASTNode node) {
		if (node == null) return SystemElement.throwNullArgumentException("node");
		
		IASTFileLocation loc = node.getFileLocation();
		if (loc == null) return SystemElement.throwNullArgumentException("location");
		return loc.getStartingLineNumber() + "@" + loc;
	}
	
	public static String toLineLocationOf(ASTNode node) {
		return toLineOffsetLocationOf(node, false);
	}
	
	public static String toLineOffsetLocationOf(ASTNode node) {
		return toLineOffsetLocationOf(node, true);
	}
	
	private static String toLineOffsetLocationOf(ASTNode node, boolean printsOffset) {
	    if (node == null) return SystemElement.throwNullArgumentException("node");
		String locPath = node.getFileName();
		return getStartingLineNumberOf(node)  
				+ (printsOffset ? "+" + node.getNodeOffset() : "") + "@"
				+ locPath.substring(locPath.lastIndexOf(File.separator) + 1).replace('.', '_');
	}
	
	public static String toBriefingOf(ASTNode node) {
		return toStringOf(node) + "\n" + toLocationOf(node);
	}

	public static String toID(IType type) {
		if (type == null) SystemElement.throwNullArgumentException("type");
		final String t = type.toString();
		return t.replace(' ', '_').replaceAll("\\*", "pt");
	}
	
	
	
	public static boolean isInTheSameFile(ASTNode node1, ASTNode node2) {
		if (node1 == node2) return true;
		if (node1 == null || node2 == null) return false;
		
		return node1.getContainingFilename().equals(node2.getContainingFilename());
	}
	
	/**
	 * @param l1
	 * @param l2
	 * @return
	 */
	public static boolean equals(IASTFileLocation l1, IASTFileLocation l2) {
		if (l1 == l2) return true;
		if (l1 == null || l2 == null) return false;
		
		return l1.getFileName().equals(l2.getFileName()) && l1.getNodeOffset() == l2.getNodeOffset();
	}
	
	/**
	 * TODO? Name.equals(...) doesn't work as expected?
	 * TODO? MethodDeclaration.equals(...) doesn't work as expected!
	 * 
	 * @param node1
	 * @param node2
	 * @return
	 */
	public static boolean equals(ASTNode node1, ASTNode node2) {
		if (node1 == node2) return true;
		if (node1 == null || node2 == null) return false;
		
		return equals(node1.getFileLocation(), node2.getFileLocation());
	}
	
	/**
	 * @param name1
	 * @param name2
	 * @param ignoresLocation - to ignore AST location equality or not?
	 * @return
	 */
	public static boolean equals(final Name name1, final Name name2, final boolean ignoresLocation) {
		if (name1 == name2) return true;
		if (name1 == null || name2 == null) return false;
		if (!ignoresLocation) return name1.equals(name2);
		
		/*
		 *  ignoresLocation - Checking binding equivalence ignoring AST location
		 *  TODO: the same Name's won't bind to the same IVariable's?
		 */
		final IBinding bind1 = name1.resolveBinding();
		final IBinding bind2 = name2.resolveBinding();
		if (bind1 == null || bind2 == null) return false;
		return bind1.equals(bind2);
	}
	
	/**
	 * @param name
	 * @param ignoresLocation - To ignore location hash code or not?
	 * @return
	 */
	public static int hashCodeOf(Name name, boolean ignoresLocation) {
		if (name == null) 
			throw new IllegalArgumentException("Can't hash code of a null ASTName!");
		
		if (ignoresLocation) {
			IBinding bind = name.resolveBinding();
			if (bind != null) return bind.hashCode();
		}
		return name.hashCode();
//		IASTFileLocation loc = name.getFileLocation();
//		return loc.getFileName().hashCode() + new Integer(loc.getNodeOffset()).hashCode();
	}


	
	/**
	 * @param types1
	 * @param types2
	 * @return
	 */
	public static boolean superclasses(Class<?>[] types1, Class<?>[] types2) {
		if (types2 == null) return false;
		
		boolean is1supering2 = false;
		for (Class<?> type2 : types2) {
			is1supering2 = superclasses(types1, type2);
			if (!is1supering2) break;
		}
		return is1supering2;
	}
	
	/**
	 * @param types1
	 * @param type2
	 * @return
	 */
	public static boolean superclasses(Class<?>[] types1, Class<?> type2) {
		if (types1 == null) return false;
		
		boolean is1supering2 = false;
		for (Class<?> type1 : types1) {
			is1supering2 = superclasses(type1, type2);
			if (!is1supering2) break;
		}
		return is1supering2;
	}
	
	/**
	 * @param type1
	 * @param type2
	 * @return
	 */
	public static boolean superclasses(Class<?> type1, Class<?> type2) {
		if (type1 == null || type2 == null) return false;
		if (type1 == type2) return true;
		
		// checking super interfaces
		for (Class<?> itf2 : type2.getInterfaces()) 
			if (superclasses(type1, itf2)) return true;

		// checking super classes
		return superclasses(type1, type2.getSuperclass());
	}
	
	
	
	public static <T> T throwASTException(ASTNode node) 
			throws ASTException {
		throw new ASTException(node);
	}
	
	public static <T> T throwASTException(IBinding bind, Exception cause) 
			throws ASTException {
		throw bind instanceof IProblemBinding
		? new ASTException((IProblemBinding) bind, cause)
		: new ASTException(bind, cause);
	}

}