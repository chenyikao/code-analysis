/**
 * 
 */
package fozu.ca;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

import fozu.ca.Elemental.TrySupplier;
import fozu.ca.vodcg.SystemElement;

/**
 * @deprecated
 * @author Kao, Chen-yi
 *
 */
@Deprecated(forRemoval=true)
public abstract class DebugElement {
	
	protected static final int DEFAULT_DEPTH = 20;
	private static boolean haltsException = false;
	
//	public <T> T get(Supplier<T> sup) {
//	return get(sup, null);
//}

//public static <T> T get(Supplier<T> sup, Function<Exception, T> alt) {
//	try {
//		return debugCallDepth((Supplier<T>) ()-> 
//		Elemental.get(sup, alt));
//		
//	} catch (Exception e) {
//		if (alt == null) throwNullArgumentException("alternative");
//		return alt.apply(e);
//	}
//}

//static public <T> T get(DebugElement caller, Supplier<T> sup, Function<Exception, T> alt) {
//return debugCallDepth(caller, ()-> Elemental.get(sup, alt));
//}

//static public <T> T getNonNull(Supplier<T> sup) {
//return debugCallDepth((Supplier<T>)
//		()-> Elemental.getNonNull(sup));
//}

	public <T> T getNonNull(Supplier<T> sup, DebugElement caller) {
		return debugCallDepth(
				DEFAULT_DEPTH, 
				(SystemElement) caller, 
				()-> Elemental.getNonNull(sup));
	}
	
	public static <T> T getSkipNull(Supplier<T> sup) {
		return debugCallDepth(null, ()-> Elemental.getSkipNull(sup));
	}
	
	public static <T> T getSkipNull(SystemElement caller, Supplier<T> sup) {
		return debugCallDepth(caller, ()-> Elemental.getSkipNull(sup));
	}
	
	public static <T> T getSkipException(SystemElement caller, Supplier<T> sup) {
		return debugCallDepth(caller, ()-> Elemental.getSkipException(sup));
	}
	
//public <T, R> R applySkipNull(
//Function<T, R> func, Supplier<T> inputSup, @SuppressWarnings("unchecked") Supplier<Boolean>... conjTesters) 
//		throws Exception {
//return debugCallDepth((Supplier<R>)
//	()-> Elemental.applySkipNull(func, inputSup, conjTesters));
//}
	
//public <T> void consumeSkipNull(
//Consumer<T> con, Supplier<T> inputSup, 
//@SuppressWarnings("unchecked") Supplier<Boolean>... conjTesters) 
//		throws Exception {
//debugCallDepth(()-> 
//Elemental.consumeSkipNull(con, inputSup, conjTesters));
//}
	
	
	
	public <T> T testsSkipNull(
			Boolean tester, Supplier<T> trueResult, Supplier<T> falseResult) {
		return debugCallDepth((Supplier<T>) ()-> 
		Elemental.testsSkipNull(tester, trueResult, falseResult));
	}
	
	
	
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
	
	public <T> T debugCallDepth(Supplier<T> call, Object... args) {
		return debugCallDepth((SystemElement) this, call, args);
	}
	
	public static <T> T debugCallDepth(
			SystemElement caller, Supplier<T> callee, Object... args) {
		return debugCallDepth(DEFAULT_DEPTH, caller, callee, args);
	}
	
	/**
	 * Debugging handles only stack overflow exceptions and throws others.
	 * 
	 * @param <T>
	 * @param depth is <em>not</em> precise since its counting may be interrupted by exception throwing
	 * @param caller
	 * @param callee
	 * @param args
	 * @return
	 */
	public static <T> T debugCallDepth(
			int depth, DebugElement caller, Supplier<T> callee, Object... args) {
		return caller == null || caller instanceof SystemElement
				? SystemElement.guard(
						(SystemElement) caller, callee, ()-> throwStackOverflowException(), depth, null, args)
						: throwTodoException("unsupported element type");
	}
	
	@SuppressWarnings("unchecked")
	public static <T, E extends Exception> T debugCallDepth(
			int depth, SystemElement caller, TrySupplier<T, E> callee, Object... args) 
					throws E {
		final List<E> nonSkips = new ArrayList<>();
		final T result = debugCallDepth(
				depth, caller, callee.toSupplier(nonSkips), args);
		if (!nonSkips.isEmpty()) throw nonSkips.get(0);
		return result;
	}
	
	public <T> T debugCallDepth(int count, Supplier<T> call, Object... args) {
		return debugCallDepth(count, (SystemElement) this, call, args);
	}
	
	public <T, E extends Exception> T debugCallDepth(
			int count, TrySupplier<T, E> call, Object... args) 
					throws E {
		return debugCallDepth(count, (SystemElement) this, call, args);
	}
	
	@SuppressWarnings("unchecked")
	public <T, E extends Exception> T debugCallDepthThrow(
			TrySupplier<T, E> call, Object... args) throws E {
		final List<E> nonSkips = new ArrayList<>();
		final T result = debugCallDepth(
				(SystemElement) this, 
				call.toSupplier(nonSkips), 
				args);
		if (!nonSkips.isEmpty()) throw nonSkips.get(0);
		return result;
	}
	
	public <T, R> R debugApply(
			Function<T, R> func, Supplier<T> input, Function<Exception, R> returnAlt, 
			@SuppressWarnings("unchecked") Supplier<Boolean>... conjTesters) {
		return debugCallDepth((SystemElement) this,
				(Supplier<R>) ()-> Elemental.apply(func, input, returnAlt, conjTesters));
	}
	
	public void debugRun(Runnable call, Object... args) {
		debugRun((SystemElement) this, call, args);
	}
	
	public static void debugRun(SystemElement caller, Runnable call, Object... args) {
		if (call == null) throwNullArgumentException("call");
		debugCallDepth(caller, ()-> {call.run(); return null;}, args);
	}
	
	public <T> T debugGet(Supplier<T> sup) {
		return debugCallDepth((SystemElement) this,
				(Supplier<T>) ()-> Elemental.getNonNullSupplier(sup));
	}
	
	public <T> T debugGet(int depth, Supplier<T> sup) {
		return debugCallDepth(depth, (SystemElement) this,
				(Supplier<T>) ()-> Elemental.getNonNullSupplier(sup));
	}
	
	public static <T> T debugGet(SystemElement caller, Supplier<T> sup, Object... args) {
		return debugCallDepth(caller, (Supplier<T>) ()-> Elemental.getNonNullSupplier(sup), args);
	}
	
	public <T> T debugGet(
			Supplier<T> sup, Function<Exception, T> alt) {
		return debugCallDepth((SystemElement) this,
				(Supplier<T>) ()-> Elemental.get(sup, alt));
	}
	
	public <T> T debugGet(
			Supplier<T> sup, Supplier<T> nullAlt) {
		return debugGet(sup, nullAlt, null);
	}
	
	public <T> T debugGet(
			Supplier<T> sup, Supplier<T> nullAlt, Function<Exception, T> excAlt) {
		return debugCallDepth((Supplier<T>) ()-> Elemental.get(sup, nullAlt, excAlt));
	}
	
	public <T> T debugGetNonNull(Supplier<T> sup) {
		return debugCallDepth((SystemElement) this,
				(Supplier<T>) ()-> Elemental.getNonNull(sup));
	}
	
	public static <T> T debugGetNonNull(SystemElement caller, Supplier<T> sup, Object... args) {
		return debugCallDepth(caller, (Supplier<T>) ()-> Elemental.getNonNull(sup), args);
	}
	
	public <T> T debugGetSkipNull(Supplier<T> sup) {
		return debugCallDepth((SystemElement) this,
				(Supplier<T>) ()-> Elemental.getSkipNull(sup));
	}
	
	public <T, E extends Exception> T debugGetThrow(
			TrySupplier<T, E> sup, Supplier<T> nullAlt) throws E {
		return debugCallDepthThrow(()-> Elemental.getThrow(sup, nullAlt));
	}
	
	public boolean debugTests(Supplier<Boolean> target) {
		return debugCallDepth((SystemElement) this,
				()-> Elemental.tests(target));
	}
	
	public <T> void debugToString(T target) {
		debug(target, Object::toString);
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

		} catch (IllegalArgumentException e1) {
			throw e1;
		} catch (Exception e) {
			return null;	
		}
	}
	
	public static <T> T throwInvalidityException(String message) 
			throws IllegalArgumentException {
		return throwInvalidityException(message, null);
	}
	
	public static <T> T throwNullArgumentException(String arg) {
		return throwNullArgumentException(arg, null);
	}
	
//	public static <T> T throwNullArgumentException(String arg, Supplier<T> returnAlt) {
//		return throwNullArgumentException(arg, null);
//	}
	
	public static <T> T throwNullArgumentException(String arg, Exception e) 
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
	 * For all unforgettable todo's, which MUST be implemented before removing the DebugElement extension!
	 * 
	 * @param message
	 * @throws UnsupportedOperationException
	 */
	public static <T> T throwTodoException(String message) {
		return throwTodoException(message, null);
	}
	
	/**
	 * For all unforgettable todo's, which MUST be implemented before removing the DebugElement extension!
	 * 
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
			
		} catch (UnsupportedOperationException e1) {
			throw e1;
		} catch (Exception e) {
			return null;	
		}
		return null;	
	}
	
}