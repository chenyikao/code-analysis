/**
 * 
 */
package fozu.ca;

import java.util.function.Consumer;
import java.util.function.Supplier;

/**
 * @author Kao, Chen-yi
 *
 */
@Deprecated(forRemoval=true)
public abstract class DebugElement {
	
	protected static final int DEFAULT_DEPTH = 20;
	private static boolean haltsException = false;
	
	public static <T> T debug(Supplier<T> subject) {
		if (subject != null) try {
			return subject.get();
		} catch (Exception e) {
			throwInvalidityException(e.toString());
		}
		return null;
	}
	
	public void debug(final Runnable subject) {
		if (subject == null) return;
		try {
			subject.run();
		} catch (Exception e) {
			throwInvalidityException(e.toString());
		}
	}
	
	public <T> void debug(T target, Consumer<T> tester) {
		if (target == null) throwInvalidityException("must provide a target");
		if (tester == null) throwInvalidityException("must provide a tester");
		try {
			tester.accept(target);
		} catch (Exception e) {
			throwInvalidityException(e.toString());
		}
	}
	
	
	
//	public void debugCallDepth(TryRunnable call) throws Exception {
//		debugCallDepth(DEFAULT_DEPTH, call);
//	}
	
//	public static <T> void debugCallDepth(TryRunnable subject) 
//			throws Exception {
//		debugCallDepth(DEFAULT_DEPTH, (SystemElement) null,
//				(TrySupplier<T>) ()-> {subject.run(); return null;});
//	}
	
	public <T> void debugToString(T target) {
		debug(target, (input)-> input.toString());
	}
	
	
	
	public static void haltException() {
		haltsException = true;
	}
	
	/**
	 * Temporarily halting for printing exception stack trace and debugging. 
	 * @param source
	 */
	public static void haltException(Exception source) {
		haltException();
		try {
			throwHaltableException(source);
		} catch (Exception e) {
			haltException();
		}
	}
	
	public static void passException() {
		haltsException = false;
//		if (this instanceof SystemElement) ((SystemElement) this).clear();
	}
	
	public static <E extends Throwable, T> T throwHaltableException(E e) 
			throws E {
		if (e == null) throwNullArgumentException("exception");
//		final Throwable cause = e.getCause();
//		if (haltsException || (cause != null && cause.getCause() != null)) {
		if (haltsException) {
			e.printStackTrace();
			passException();
		}
		throw e;
	}
	
	public static <T> T throwUnhandledException(Exception source) {
		return throwInvalidityException("unhandled exception", source);
	}
	
	public static <T> T throwIllegalStateException(String msg) 
			throws IllegalStateException {
		return throwHaltableException(new IllegalStateException(msg));
	}
	
	/**
	 * For all easily intercept-able exception breakpoints!
	 * 
	 * @param message
	 * @param source 
	 * @throws IllegalArgumentException
	 */
	public static <T> T throwInvalidityException(
			String message, Exception source) 
			throws IllegalArgumentException {
		if (message == null) throwNullArgumentException("message");
		
		try {
			haltException();
			message = "Invalid: " + message + "! Please contact the development team!";
			source = source == null 
					? new IllegalArgumentException(message)
					: new IllegalArgumentException(message, source);
			return throwHaltableException(source);

		} catch (Exception e1) {
			if (e1 instanceof IllegalArgumentException) throw (IllegalArgumentException) e1;
		}
		return null;	
	}
	
	public static <T> T throwInvalidityException(String message) 
			throws IllegalArgumentException {
		return throwInvalidityException(message, null);
	}
	
	public static <T> T throwNullArgumentException(String arg) {
		return throwNullArgumentException(arg, null, null);
	}
	
	public static <T> T throwNullArgumentException(String arg, Supplier<T> returnAlt) {
		return throwNullArgumentException(arg, returnAlt, null);
	}
	
	public static <T> T throwNullArgumentException(String arg, Exception e) {
		return throwNullArgumentException(arg, null, e);
	}
	
	public static <T> T throwNullArgumentException(String arg, Supplier<T> returnAlt, Exception e) 
			throws IllegalArgumentException {
		haltException();
		return throwHaltableException(new IllegalArgumentException("must provide some " + arg, e));
	}
	
	public static <T> T throwStackOverflowException() 
			throws StackOverflowError {
		haltException();
		return throwHaltableException(new StackOverflowError("stack overflow?"));
	}
	
	public static <T> T throwReductionException() 
			throws UnsupportedOperationException {
		return throwTodoException("true reduction");
	}
	
	public static <T> T throwTodoException(Exception cause) {
		return throwTodoException(null, cause);
	}
	
	/**
	 * For all unforgettable todo's!
	 * 
	 * @param message
	 * @throws UnsupportedOperationException
	 */
	public static <T> T throwTodoException(String message) {
		return throwTodoException(message, null);
	}
	
	/**
	 * For all unforgettable todo's!
	 * @param message
	 * @param cause
	 * @throws UnsupportedOperationException
	 */
	public static <T> T throwTodoException(String message, Exception cause) {
		if (message == null) message = "unhandled exception";
		
		try {
			haltException();
			if (cause == null) cause = new UnsupportedOperationException(
					"Sorry and please contact the development team to finish this task:\n" + message + "?");
			throwHaltableException(cause);
			
		} catch (Exception e1) {
			if (e1 instanceof UnsupportedOperationException) throw (UnsupportedOperationException) e1;
		}
		return null;	
	}
	
}