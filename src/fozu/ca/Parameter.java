package fozu.ca;

import fozu.ca.condition.Type;

public class Parameter extends Pair<String, Type> {
	
	public Parameter(String name, Type type) {
		super(name, type);
	}
	
	static public String getDefaultName(int index) {
		return "_" + String.valueOf(index);
	}
	
}