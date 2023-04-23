/**
 * 
 */
package fozu.ca;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * @author Kao, Chen-yi
 *
 */
public class StarMatcher {

	private String input;
	private Pattern p;
	private Matcher m;
	
	@SuppressWarnings("deprecation")
	public StarMatcher(final Pattern pattern, final String input) {
		if (pattern == null) DebugElement.throwNullArgumentException("pattern");
		if (input == null) DebugElement.throwNullArgumentException("input");

		this.input = input;
		p = pattern;
		m = p.matcher(input);
	}
	
	public boolean find() {
		return m.find();
	}

	public String group(String name) {
		String g = null;
		try {
			g = m.group(name);

		} catch (IllegalStateException | IllegalArgumentException e) {
			// ex. m.start("listItem") > m.end("firstListItem")
			m = p.matcher(input);
			g = m.group(name);
		}
		input = m.replaceFirst("");
		return g;
	}
	
}