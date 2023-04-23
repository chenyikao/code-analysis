package fozu.ca.solver;
import java.io.IOException;

/**
 * 
 */

/**
 * @author Kao, Chen-yi
 *
 */
abstract public class Degrading {

	abstract protected String degradeFormulae();
	
	public String check() throws IOException {
		// TODO: parameterize Solver
		return Solver.z3check(degradeFormulae());
	}

}
