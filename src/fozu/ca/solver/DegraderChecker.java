package fozu.ca.solver;
import java.io.IOException;
import java.util.NoSuchElementException;

/**
 * @author Kao, Chen-yi
 *
 */
abstract public class DegraderChecker<DegradingClass extends Degrading> {

	/**
	 * @return
	 * @throws NoSuchElementException - Following the behavior of {@link java.util.Iterator} that the first 
	 * 	{@link java.util.Iterator#next()} call returns the first element. Hence every element getting before 
	 * 	the first next call shall return null or no such element exception.
	 */
	abstract public DegradingClass getCurrentDegrading() throws NoSuchElementException;
	public String getCurrentDegradingString() throws NoSuchElementException {return getCurrentDegrading().toString();}
	
	abstract protected DegradingClass nextDegrading() throws NoSuchElementException;
	public String nextCheck() throws NoSuchElementException, IOException {return nextDegrading().check();}
	abstract public void resetCheck();
	
}
