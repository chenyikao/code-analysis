/**
 * 
 */
package fozu.ca.vodcg.condition.data;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.IName;
import org.eclipse.jdt.core.dom.IASTInitializerClause;
import org.eclipse.jdt.core.dom.IASTSimpleDeclSpecifier;
import org.eclipse.jdt.core.dom.IArrayType;
import org.eclipse.jdt.core.dom.IBasicType;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.ICompositeType;
import org.eclipse.jdt.core.dom.IEnumeration;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.IPointerType;
import org.eclipse.jdt.core.dom.IQualifierType;
import org.eclipse.jdt.core.dom.IType;
import org.eclipse.jdt.core.dom.IValue;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;

import fozu.ca.DebugElement;
import fozu.ca.condition.SerialFormat;
import fozu.ca.vodcg.ASTException;
import fozu.ca.vodcg.ASTUtil;
import fozu.ca.vodcg.SystemElement;
import fozu.ca.vodcg.condition.ConditionElement;
import fozu.ca.vodcg.condition.Expression;

/**
 * For declaring variable and function return type.
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings({ "deprecation", "removal" })
public enum DataType implements PlatformType {
	Int {
		@Override
		public boolean isCastableTo(PlatformType type2) {
			return type2 instanceof PointerType || super.isCastableTo(type2);
		}
		
	}, Real, Bool, Char, Void;
	public static final ArrayType Array = ArrayType.PRIMITIVE_ARRAY_TYPE;
	public static final PointerType Pointer = PointerType.NULL_POINTER_TYPE;
	public static final PointerType String = PointerType.from(Char);

	
	
	public static PlatformType from(ITypeBinding type) {
		if (type == null) DebugElement.throwNullArgumentException("type");

        if (type.isEnum())
            return ASTUtil.isBinary(type) ? Bool : Int;
        
        if (type.isArray()) {
            return ArrayType.from(
                    from(type.getElementType()), 
                    fozu.ca.vodcg.condition.data.Int.from(type.getDimensions(), null));
        }
        
		switch (type.getQualifiedName()) {
		case "bool", "java.lang.Boolean":	return Bool;
		
		case "char", "java.lang.Character",
		"java.lang.String":					return Char;
		
		case "int", "java.lang.Integer",
		"byte", "java.lang.Byte",
		"short", "java.lang.Short",
		"long", "java.lang.Long",
		"java.math.BigInteger",
		"java.util.concurrent.atomic.AtomicInteger",
		"java.util.concurrent.atomic.AtomicLong": 	return Int;
		
		case "float", "java.lang.Float",
		"double", "java.lang.Double",
		"java.math.BigDecimal":				return Real;
		
		case "void":						return Void;
		
		default:
		}

		PointerType dt = new PointerType(false);
		
		if (type instanceof IPointerType) {
			dt.pointTo(from(((IPointerType) type).getType()));
			return dt;
		}
		
		DebugElement.throwTodoException("type instanceof OtherType");
		return null;
	}
	
	public static PlatformType from(IName name) {
		if (name == null) DebugElement.throwNullArgumentException("AST name");
		return from(ASTUtil.getBindingOf(name));
	}
	
	public static PlatformType from(IBinding bind) {
		if (bind == null) DebugElement.throwNullArgumentException("binding");
		
		if (bind instanceof IVariableBinding) 
			return from(((IVariableBinding) bind).getType());
		else if (bind instanceof ITypeBinding) 
			return from((ITypeBinding) bind);
		else if (bind instanceof IMethodBinding) 
			return from(((IMethodBinding) bind).getReturnType());
		
		DebugElement.throwTodoException("bind instanceof OtherClass");
		return null;
	}
	
//	public static PlatformType from(final IASTSimpleDeclSpecifier decl) 
//			throws ASTException {
//		if (decl == null) SystemElement.throwNullArgumentException("declaration specifier");
//		
//		final int dt = decl.getType();
//		switch (dt) {
//		case IASTSimpleDeclSpecifier.t_bool:			return Bool;
//		case IASTSimpleDeclSpecifier.t_char:
//		case IASTSimpleDeclSpecifier.t_char16_t:
//		case IASTSimpleDeclSpecifier.t_char32_t:
//		case IASTSimpleDeclSpecifier.t_wchar_t:			return Char;
//		case IASTSimpleDeclSpecifier.t_int:
//		case IASTSimpleDeclSpecifier.t_int128:			return Int;
//		case IASTSimpleDeclSpecifier.t_double:
//		case IASTSimpleDeclSpecifier.t_float:
//		case IASTSimpleDeclSpecifier.t_float128:
//		case IASTSimpleDeclSpecifier.t_decimal32:
//		case IASTSimpleDeclSpecifier.t_decimal64:
//		case IASTSimpleDeclSpecifier.t_decimal128:		return Real;
//		case IASTSimpleDeclSpecifier.t_void:			return Void;
//		case IASTSimpleDeclSpecifier.t_unspecified:
//			ASTUtil.throwASTException(decl);
//			
//		case IASTSimpleDeclSpecifier.t_auto:
//		case IASTSimpleDeclSpecifier.t_decltype:
//		case IASTSimpleDeclSpecifier.t_decltype_auto:
//		case IASTSimpleDeclSpecifier.t_typeof:
//		default:
//			SystemElement.throwTodoException("Unsupported type: " + dt);
//		}
//
//		return null;
//	}
	
//	public DataType fromJavaType(javaType) throws NonSupportedTypeException {	// TODO: NonSupportedType
//		return;
//	}



//	public static IType[] getTypesOf(IASTInitializerClause[] args) {
//		List<IType> types = new ArrayList<IType>();
//		for (IASTInitializerClause arg : args) {
//			if (arg instanceof org.eclipse.jdt.core.dom.Expression) 
//				types.add(((org.eclipse.jdt.core.dom.Expression) arg).getExpressionType());
//			// TODO: else ...
//		}
//		return (IType[]) types.toArray();
//	}

	public static PlatformType[] getTypesOf(Expression[] args) {
		final List<PlatformType> types = new ArrayList<>();
		for (Expression arg : args) types.add(arg.getType());
		return (DataType[]) types.toArray();
	}
	

	
	@Override
	public java.lang.String getID(SerialFormat format) {
		return toNonEmptyString(false);
	}
	
	/**
	 * Ignoring {@link #Array} and {@link #Pointer}.
	 * 
	 * @see fozu.ca.vodcg.condition.data.Type#getDimension()
	 */
	public int getDimension() {
		return 0;
		//	TODO:
//			switch (this) {
//			case Bool:
//			case Char:
//			case Int:
//			case Real:
//			case Array:
//			case Pointer:
//				return ((Pointer) this).getDimension();
//			default:
//			}
	}

	@Override
	public Number<?> getPositiveInfinity() {
		switch (this) {
		case Int:	return fozu.ca.vodcg.condition.data.Int.POSITIVE_INFINITY;
		case Real:	return fozu.ca.vodcg.condition.data.Real.POSITIVE_INFINITY;
		case Bool:
		case Char:
		default:
		}
		return null;	// non-defined infinity
	}

	@Override
	public Number<?> getNegativeInfinity() {
		switch (this) {
		case Int:	return fozu.ca.vodcg.condition.data.Int.NEGATIVE_INFINITY;
		case Real:	return fozu.ca.vodcg.condition.data.Real.NEGATIVE_INFINITY;
		case Bool:
		case Char:
		default:
		}
		return null;	// non-defined infinity
	}

	
	
//	/**
//	 * Ignoring {@link #Array} and {@link #Pointer}.
//	 * 
//	 * @return
//	 */
//	public Type getPointTo() {
//		return this;
//	}
//	
//	/**
//	 * Ignoring {@link #Array} and {@link #Pointer}.
//	 * 
//	 * @return
//	 */
//	public Expression getPointToEnd() {
//		return null;
//	}
//	
//	/**
//	 * Ignoring {@link #Array} and {@link #Pointer}.
//	 * 
//	 * @see fozu.ca.vodcg.condition.data.Type#pointTo(fozu.ca.vodcg.condition.data.Type)
//	 */
//	public void pointTo(Type type) {
//	}
	
	

	/**
	 * @return true if this data type is <em>naturally bounded</em>.
	 */
	public boolean isBounded() {
		switch (this) {
		case Bool:
		case Char:
		case Void:	return true;
		case Int:
		case Real:
		default:
		}
		return false;
	}
	
	@Override
	public boolean isNumeric() {
		switch (this) {
		case Int:
		case Real:	return true;
		case Bool:
		case Char:
		case Void:
		default:
		}
		return false;
	}
	
	@Override
	public boolean isPrimitive() {
		switch (this) {
		case Int:
		case Real:
		case Bool:
		case Char:
		case Void:	return true;
		default:
		}
		return false;
	}
	

	
	/**
	 * For this enumeration that can't extend {@link ConditionElement}.
	 * 
	 * @param usesParenthesesAlready
	 * @return
	 * @see fozu.ca.vodcg.condition.ConditionElement#toNonEmptyString(boolean)
	 */
	public java.lang.String toNonEmptyString(boolean usesParenthesesAlready) {
		return toZ3SmtString(false, false);
	}

	/**
	 * Ignoring {@link #Array} and {@link #Pointer}.
	 * @see fozu.ca.vodcg.condition.data.Type#toZ3SmtString(boolean, boolean, boolean)
	 */
	@Override
	public java.lang.String toZ3SmtString(
			boolean printsVariableDeclaration, boolean printsFunctionDefinition) {
		switch (this) {
		case Int: 		return "Int";
		case Real:		return "Real";
		case Bool:		return "Bool";
		case Char:		return fozu.ca.vodcg.condition.data.Char.toTypeString(SerialFormat.Z3_SMT);
		case Void:		return "Void";
		default:
			DebugElement.throwTodoException("unsupported data type");
			return null;
		}
	}
	
	public java.lang.String toZ3SmtPointableTypeOperator() {
		switch (this) {
		case Int: 		return "i2pt";
		case Real:		return "r2pt";
		case Bool:		return "b2pt";
		case Char:		return "c2pt";
		case Void:		return "v2pt";
		default:
			DebugElement.throwTodoException("unsupported data type");
			return null;
		}
	}

}