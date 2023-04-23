package fozu.ca.condition;

import fozu.ca.DebugElement;

/**
 * A Z3-SMT-compatible data category like a primitive {@link DataType} 
 * or structured {@link Pointer}.
 * 
 * @author Kao, Chen-yi
 *
 */
public interface Type {

	/**
	 * @param format
	 * @return ID string without white-space characters.
	 */
	public java.lang.String getID(SerialFormat format);
	
	public boolean isNumeric();
	public boolean isPrimitive();
	


	default public <T> T throwTypeException() {
		return DebugElement.throwTodoException("unsupported type");
	}
	
	/**
	 * For {@link DataType} that can't extend {@link ConditionElement}.
	 * 
	 * @param printsVariableDeclaration
	 * @param printsFunctionDefinition
	 * @return
	 * @see {@link fozu.ca.condition.ConditionElement#toZ3SmtString(boolean, boolean)}
	 */
	public java.lang.String toZ3SmtString(
			boolean printsVariableDeclaration, boolean printsFunctionDefinition);

}