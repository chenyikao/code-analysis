package fozu.ca.vodcg.condition;

import java.util.Arrays;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.index.IIndexName;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Statement;
import org.eclipse.jdt.core.dom.StructuralPropertyDescriptor;

import fozu.ca.condition.SerialFormat;
import fozu.ca.vodcg.Assignable;
import fozu.ca.vodcg.ASTAddressable;
import fozu.ca.vodcg.SystemElement;
import fozu.ca.vodcg.VODCondGen;
import fozu.ca.vodcg.condition.data.PlatformType;
import fozu.ca.vodcg.util.ASTUtil;
import fozu.ca.vodcg.condition.data.DataType;

/**
 * @author Kao, Chen-yi
 *
 */
public abstract class Referenceable extends Expression 
implements ASTAddressable {

	private String name;
	private Name cName;
	private IIndexName enclosingDefinition = null;	// optional

	private PlatformType type;	// for caching type
	
	/**
	 * @param name
	 * @param cName
	 * @param enclosingDefinition
	 * @param type - maybe null if subject is later provided
	 * @param condGen
	 */
	private Referenceable(String name, Name cName, 
			IIndexName enclosingDefinition, PlatformType type, 
			final ASTAddressable rtAddr, VODCondGen condGen) {
		super(rtAddr, condGen);

		this.enclosingDefinition = enclosingDefinition;
		if (name != null) setName(name);
		if (cName != null) setName(cName);
		if (type != null) initType(type);
	}
	
	/**
	 * For non-AST expressions.
	 * 
	 * @param name
	 * @param type
	 * @param condGen
	 */
	protected Referenceable(String name, PlatformType type, VODCondGen condGen) {
		this(name, null, null, type, null, condGen);	// non-AST (general) Function's need no Name's
//		if (type == null) throw ILLEGAL_TYPE_EXCEPTION;
	}
	
	/**
	 * @param name
	 * @param type
	 * @param condGen 
	 */
	protected Referenceable(Name name, PlatformType type, final ASTAddressable rtAddr, VODCondGen condGen) {
		this(	name.toString(), 
				name, 
				null, 
				type != null ? type : DataType.from(name), 
				rtAddr, 
				condGen);
	}
	
	protected Referenceable(Name name, IBinding bind, final ASTAddressable rtAddr, VODCondGen condGen) {
		this(	name == null ? bind.getName() : name.toString(),
				name,
				null,
				bind == null ? null : DataType.from(bind), 
				rtAddr, 
				condGen);
	}
	
	/**
	 * A copy constructor for the reference-able {@link Reference}'s subject.
	 * 
	 * @param subject - null if supplier is provided elsewhere.
	 * @param condGen 
	 */
	protected Referenceable(Referenceable subject, VODCondGen condGen) {
		this(null, subject, condGen);
	}
	
	/**
	 * A copy constructor for the reference-able {@link Reference}'s subject.
	 * 
	 * @param subject - null if supplier is provided elsewhere.
	 * @param condGen 
	 */
	protected Referenceable(String name, Referenceable subject, VODCondGen condGen) {
		this(	name != null ? name : (subject != null ? subject.name : null),
				subject != null ? subject.cName : null, 
				subject != null ? subject.enclosingDefinition : null, 
				subject != null ? subject.type : null, 
				subject != null ? subject.getRuntimeAddress() : null, 
				condGen);
	}
	

	
	/**
	 * Not override-able since sub-classes' initType(..) may be called during super-construction 
	 * and before they're initialized and ready for type-checking.
	 * 
	 * Type-checking is done later at {@link #setType(PlatformType)}.
	 * 
	 * @param newType
	 */
	private void initType(PlatformType newType) {
		type = newType;
	}
	

	
	/**
	 * @return a non-empty String
	 */
	@SuppressWarnings("removal")
	@Override
	public String getName() {
		if (cName != null && name == null) {
			name = cName.toString();
//			if (!cn.equals(name)) throwTodoException("inconsistent names");
		} else 
			if (name == null || name.isBlank()) throwTodoException("no names");
		return name;
	}
	
//	/**
//	 * @return C name in {@link Name} form.
//	 */
//	public Name getIName() {
//		return cName;
//	}
	
	public final String peekName() {
		return name;
	}
	
	@Override
	public ASTNode getASTAddress() {
		return getASTName();
	}
	
	/**
	 * @return Java name in {@link Name} form.
	 */
	public Name getASTName() {
		return isInAST() ? peekASTName() : null;
	}

	public final Name peekASTName() {
		return ASTUtil.toASTName(cName);
	}
	
	public void setName(Name newName) {
		if (newName == null) throwNullArgumentException("name");
		cName = newName;
	}
	
	public void setName(String newName) {
		// Whitespace's are not allowed
		if (newName == null || newName.isBlank()) throwNullArgumentException("name");
//		if (!newName.matches("\\S+")) throwTodoException("unsupported name pattern");
		if (cName != null && !newName.contains(cName.toString())) throwTodoException("inconsistent names");

		name = newName;
	}

	
	
	@Override
	public String getIDSuffix(final SerialFormat format) {
		return getNonNull(()-> getType().getID(format));
	}
	
	@Override
	public Statement getPrivatizingBlock() {
		return isInAST()
				? Assignable.from(getASTName(), cacheRuntimeAddress(), getCondGen())
						.getPrivatizingBlock()
				: null;
	}

	
	
	@Override
	public PlatformType getType() {
		return type;
	}
	
	public String getZ3SmtType(boolean printsVariableDeclaration) {
		final PlatformType t = getType();
		return t == null 
				? "?" 
				: t.toZ3SmtString(printsVariableDeclaration, false); 
	}
	
	public void setType(PlatformType newType) {
		if (newType == null) throwNullArgumentException("type");
//		if (type != null && newType != type) throwTodoException("suitable type overwriting");
		initType(newType);
	}


	
//	/**
//	 * Copy setter.
//	 * @param ref
//	 */
//	public void copy(Referenceable ref) {
//		if (ref == null) {
//			cName = null;
//			name = null;
//			enclosingDefinition = null;
//			setType(null);
//		} else {
//			cName = ref.cName;
//			name = ref.name;
//			enclosingDefinition = ref.enclosingDefinition;
//			setType(ref.getType());
//		}
//	}
	
	@SuppressWarnings("deprecation")
	@Override
	protected Boolean cacheConstant() {
		try {
			return applySkipNull(
					name-> Assignable.from(name, cacheRuntimeAddress(), getCondGen()).isConstant(), 
					()-> getASTName());
		} catch (Exception e) {
			return throwUnhandledException(e);
		}
	}
	
	@SuppressWarnings("unchecked")
	@Override
	protected Boolean cacheGlobal() {
		return debugApply(cName-> ASTUtil.isGlobal(cName),
				()-> getASTName(),
				e-> super.cacheGlobal());
	}
	

	
	@Override
	public boolean isInAST() {
		return peekASTName() != null;
	}
	
	public void setNonAST() {
		cName = null;
	}

	

	/* (non-Javadoc)
	 * @see fozu.ca.condition.ConditionElement#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		return getName().isBlank();
	}

	
	
	public boolean equalsName(final String name) {
		return cName != null && cName.toString().equals(name);
	}
	
	@Override
	protected boolean equalsToCache(SystemElement e2) {
		// while {@link Reference} do concern location equality!
		return equalsWithoutLocality(e2, true);	
	}

	/**
	 * For locality-aware sub-types such as {@link Reference}.
	 * 
	 * @param e2
	 * @param ignoresLocation
	 * @return
	 */
	protected boolean equalsWithoutLocality(SystemElement e2, boolean ignoresLocation) {
		Referenceable refb2 = (Referenceable) e2;
		if (cName != null && cName instanceof IASTName) 
			return ASTUtil.equals((IASTName)cName, (IASTName)refb2.cName, 
					ignoresLocation);
		else if (name != null && type != null)
			return name.equals(refb2.name) 
					&& type.equals(refb2.type) 
					&& super.equalsToCache(e2);
		
		return false;
	}
	
	@Override
	protected List<Integer> hashCodeVars() {
		// while {@link Reference} do concern location equality!
		return hashCodeVarsWithLocality(isInAST());	
	}
	
	/**
	 * For locality-aware sub-types such as {@link Reference}.
	 * 
	 * @param ignoresLocation TODO
	 * @return
	 */
	protected List<Integer> hashCodeVarsWithLocality(boolean ignoresLocation) {
		return Arrays.asList(cName != null && cName instanceof IASTName 
				? ASTUtil.hashCodeOf((IASTName)cName, ignoresLocation) 
				: (name != null ? name.hashCode() : 0), 
				type != null ? type.hashCode() : 0);
	}
	
	
	
	/**
	 * @return
	 */
	public String toReferenceString() {
		return getID(null);
	}

	public String toFullString() {
		if (cName == null) return name;
		else {
			StructuralPropertyDescriptor cLoc = cName.getLocationInParent();
			return name + ":" + cLoc.getStartingLineNumber() + "@" + cLoc.getFileName();
		}
	}
	
	protected String toNonEmptyString(boolean usesParenAlready) {
		return toFullString();
	}
	
	
	
//	public String disambiguateString(SerialFormat format, 
//			String originalTerm, String disambiguousTerm) {
//		if (VODCondGen.isAmbiguous(this, originalTerm, format)) {
//			if (disambiguousTerm == null) 
//				throwTodoException(originalTerm + "_conflict!");
//			else if (VODCondGen.isAmbiguous(this, disambiguousTerm, format)) 
//				throwTodoException(disambiguousTerm + "_conflict!");
////			else disambiguousTerm = disambiguousTerm; 
//		} else disambiguousTerm = originalTerm; 
//
//		if (format != null) switch (format) {
////		case Z3:	return toZ3String();
//		case Z3_SMT:
//			disambiguousTerm = disambiguateZ3SmtString(disambiguousTerm, null);
//		default:
//		}
//		
//		return disambiguousTerm;
//	}
//	
//	public String disambiguateZ3SmtString(
//			String originalTerm, String disambiguousTerm) {
//		if (originalTerm == null) throwNullArgumentException("valid terms");
//
//		return originalTerm.equals("fp") ? "_fp" : originalTerm;
//	}
	
	
	
	@Override
	public String toZ3SmtString(boolean printsVariableDeclaration, 
			boolean printsFunctionDefinition, boolean isLhs) {
		return getID(SerialFormat.Z3_SMT);
	}

}