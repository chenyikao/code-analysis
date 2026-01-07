/**
 * 
 */
package fozu.ca.vodcg.condition.data;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.Type;

import org.eclipse.jdt.core.dom.PrimitiveType;

import fozu.ca.DebugElement;
import fozu.ca.condition.SerialFormat;
import fozu.ca.vodcg.ASTException;
import fozu.ca.vodcg.SystemElement;
import fozu.ca.vodcg.condition.ConditionElement;
import fozu.ca.vodcg.condition.Expression;
import fozu.ca.vodcg.util.ASTUtil;

/**
 * For declaring variable and function return type.
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings({ "removal" })
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

	
	
	@SuppressWarnings("deprecation")
    public static PlatformType from(ITypeBinding type) {
		if (type == null) DebugElement.throwNullArgumentException("type");

        if (type.isEnum())
            return ASTUtil.isBinary(type) ? Bool : Int;
        
        if (type.isArray()) {
            return ArrayType.from(
                    from(type.getComponentType()), 
                    fozu.ca.vodcg.condition.data.Int.from(type.getDimensions(), null));
        }
        
        if (type.isTypeVariable()) return DebugElement.throwTodoException("type variable");
        
        final PlatformType t = from(type.getQualifiedName());
        if (t != null) return t;
        
		PointerType dt = new PointerType(false);
//		dt.pointTo(from(((IPointerType) type).getType()));
		return dt;
	}
	
	@SuppressWarnings("deprecation")
    public static PlatformType from(final java.lang.String type) {
        switch (type) {
        case "bool", "java.lang.Boolean":         return Bool;
        
        case "char", "java.lang.Character",
        "java.lang.String":                       return Char;
        
        case "int", "java.lang.Integer",
        "byte", "java.lang.Byte",
        "short", "java.lang.Short",
        "long", "java.lang.Long",
        "java.math.BigInteger",
        "java.util.concurrent.atomic.AtomicInteger",
        "java.util.concurrent.atomic.AtomicLong": return Int;
        
        case "float", "java.lang.Float",
        "double", "java.lang.Double",
        "java.math.BigDecimal":                   return Real;
        
        case "null", "void":                      return Void;
        
        default:
            return DebugElement.throwTodoException("Unsupported type: " + type);            
        }
	}
	
	public static PlatformType from(Name name) {
		if (name == null) DebugElement.throwNullArgumentException("AST name");
		return from(ASTUtil.getBindingOf(name));
	}
	
	@SuppressWarnings("deprecation")
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
	
	@SuppressWarnings("deprecation")
    public static PlatformType from(final Type type) 
			throws ASTException {
		if (type == null) SystemElement.throwNullArgumentException("declaration type");
		
		if (type.isPrimitiveType()) {
			// for primitive type cast
			final PrimitiveType.Code code = ((PrimitiveType) type).getPrimitiveTypeCode();
			if (PrimitiveType.BOOLEAN.equals(code)) return Bool;
			if (PrimitiveType.CHAR.equals(code)) return Char;
			if (PrimitiveType.BYTE.equals(code) || PrimitiveType.INT.equals(code) || PrimitiveType.LONG.equals(code) || PrimitiveType.SHORT.equals(code)) return Int;
			if (PrimitiveType.DOUBLE.equals(code) || PrimitiveType.FLOAT.equals(code)) return Real;
			if (PrimitiveType.VOID.equals(code)) return Void;
			SystemElement.throwTodoException("Unsupported type: " + code);
			
		} else if (type.isArrayType()) {
		    // for array cast
			SystemElement.throwTodoException("array type");
			
		} else {
			// for pointer cast
		    return DataType.from(type.resolveBinding());
//		    if (pt instanceof DataType) 
//		        pt = PointerType.from((DataType) pt); 
//		    else throwTodoException("unsupported cast type");
		}
//		for (@SuppressWarnings("unused") IASTPointerOperator p : type.getAbstractDeclarator().getPointerOperators())
//		    pt = PointerType.from(pt); 

		return null;
	}
	
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
	@SuppressWarnings("deprecation")
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
	
	@SuppressWarnings("deprecation")
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