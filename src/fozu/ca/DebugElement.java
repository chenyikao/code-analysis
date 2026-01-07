/**
 * 
 */
package fozu.ca;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

import fozu.ca.vodcg.SystemElement;

/**
 * @deprecated
 * @author Kao, Chen-yi
 *
 */
@Deprecated(forRemoval=true)
public abstract class DebugElement extends Elemental {
	
	@Deprecated
	protected static final int DEFAULT_DEPTH = 20;
	
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

	
	
    @Deprecated
	public static Method getMethod(
            Class<?> clazz, String name, Class<?>... parameterTypes) {
        if (clazz == null || name == null) return null;
        try {
            return clazz.getDeclaredMethod(name, parameterTypes);
            
        } catch (NoSuchMethodException | SecurityException e) {
            return DebugElement.throwTodoException(e.toString());
        }   
    }
    
    
    
//static public <T> T getNonNull(Supplier<T> sup) {
//return debugCallDepth((Supplier<T>)
//		()-> Elemental.getNonNull(sup));
//}

	@Deprecated
	public <T> T getNonNull(Supplier<T> sup, DebugElement caller) {
		return debugCallDepth(
				DEFAULT_DEPTH, 
				(SystemElement) caller, 
				()-> Elemental.getNonNull(sup));
	}
	
	@Deprecated
	public static <T> T getSkipNull(Supplier<T> sup) {
		return debugCallDepth(null, ()-> Elemental.getSkipNull(sup));
	}
	
	@Deprecated
	public static <T> T getSkipNull(SystemElement caller, Supplier<T> sup) {
		return debugCallDepth(caller, ()-> Elemental.getSkipNull(sup));
	}
	
	@Deprecated
	public static <T> T getSkipException(SystemElement caller, Supplier<T> sup) {
		return debugCallDepth(caller, ()-> Elemental.getSkipException(sup));
	}
	
    @Deprecated
	public static <T> boolean addSkipNull(Collection<T> col, Supplier<T> eleSup, Supplier<Boolean> tester,
            List<Class<? extends Exception>> skips) throws Exception {
        if (col instanceof List<?>) col = new ArrayList<>(col != null ? col : Collections.emptyList()); 
        else if (col instanceof Set<?>) col = new HashSet<>(col != null ? col : Collections.emptySet());
        else if (col != null) throwTodoException("unsupported collection");
        
        return tester == null 
                ? Elemental.addSkipNull(col, eleSup, skips) 
                : Elemental.addSkipNull(col, eleSup, skips, tester);
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
	
	
	
	@Deprecated
	public static <T> T debug(Supplier<T> subject) {
		if (subject != null) try {
			return subject.get();
		} catch (Exception e) {
			Elemental.throwInvalidityException(e.toString());
		}
		return null;
	}
	
	@Deprecated
	public void debug(final Runnable subject) {
		if (subject == null) return;
		try {
			subject.run();
		} catch (Exception e) {
		    Elemental.throwInvalidityException(e.toString());
		}
	}
	
	@Deprecated
	public <T> void debug(T target, Consumer<T> tester) {
		if (target == null) Elemental.throwInvalidityException("must provide a target");
		if (tester == null) Elemental.throwInvalidityException("must provide a tester");
		try {
			tester.accept(target);
		} catch (Exception e) {
		    Elemental.throwInvalidityException(e.toString());
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
	
	@Deprecated
	public <T> T debugCallDepth(Supplier<T> call, Object... args) {
		return debugCallDepth((SystemElement) this, call, args);
	}
	
	@Deprecated
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
	@Deprecated
	public static <T> T debugCallDepth(
			int depth, DebugElement caller, Supplier<T> callee, Object... args) {
		return caller == null || caller instanceof SystemElement
				? SystemElement.guard(
						(SystemElement) caller, callee, Elemental::throwStackOverflowException, depth, null, args)
						: throwTodoException("unsupported element type");
	}
	
	@Deprecated
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
	
	@Deprecated
	public <T> T debugCallDepth(int count, Supplier<T> call, Object... args) {
		return debugCallDepth(count, (SystemElement) this, call, args);
	}
	
	@Deprecated
	public <T, E extends Exception> T debugCallDepth(
			int count, TrySupplier<T, E> call, Object... args) 
					throws E {
		return debugCallDepth(count, (SystemElement) this, call, args);
	}
	
	@Deprecated
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
	
	@Deprecated
	public <T, R> R debugApply(
			Function<T, R> func, Supplier<T> input, Function<Exception, R> returnAlt, 
			@SuppressWarnings("unchecked") Supplier<Boolean>... conjTesters) {
		return debugCallDepth((SystemElement) this,
				(Supplier<R>) ()-> Elemental.apply(func, input, returnAlt, conjTesters));
	}
	
	@Deprecated
	public void debugRun(Runnable call, Object... args) {
		debugRun((SystemElement) this, call, args);
	}
	
	@Deprecated
	public static void debugRun(SystemElement caller, Runnable call, Object... args) {
		if (call == null) Elemental.throwNullArgumentException("call");
		debugCallDepth(caller, ()-> {call.run(); return null;}, args);
	}
	
	@Deprecated
	public <T> T debugGet(Supplier<T> sup) {
		return debugCallDepth((SystemElement) this,
				(Supplier<T>) ()-> Elemental.getNonNullSupplier(sup));
	}
	
	@Deprecated
	public <T> T debugGet(int depth, Supplier<T> sup) {
		return debugCallDepth(depth, (SystemElement) this,
				(Supplier<T>) ()-> Elemental.getNonNullSupplier(sup));
	}
	
	@Deprecated
	public static <T> T debugGet(SystemElement caller, Supplier<T> sup, Object... args) {
		return debugCallDepth(caller, (Supplier<T>) ()-> Elemental.getNonNullSupplier(sup), args);
	}
	
	@Deprecated
	public <T> T debugGet(
			Supplier<T> sup, Function<Exception, T> alt) {
		return debugCallDepth((SystemElement) this,
				(Supplier<T>) ()-> Elemental.get(sup, alt));
	}
	
	@Deprecated
	public <T> T debugGet(
			Supplier<T> sup, Supplier<T> nullAlt) {
		return debugGet(sup, nullAlt, null);
	}
	
	@Deprecated
	public <T> T debugGet(
			Supplier<T> sup, Supplier<T> nullAlt, Function<Exception, T> excAlt) {
		return debugCallDepth((Supplier<T>) ()-> Elemental.get(sup, nullAlt, excAlt));
	}
	
	@Deprecated
	public <T> T debugGetNonNull(Supplier<T> sup) {
		return debugCallDepth((SystemElement) this,
				(Supplier<T>) ()-> Elemental.getNonNull(sup));
	}
	
	@Deprecated
	public static <T> T debugGetNonNull(SystemElement caller, Supplier<T> sup, Object... args) {
		return debugCallDepth(caller, (Supplier<T>) ()-> getNonNull(sup), args);
	}
	
	@Deprecated
	public <T> T debugGetSkipNull(Supplier<T> sup) {
		return debugCallDepth((SystemElement) this,
				(Supplier<T>) ()-> getSkipNull(sup));
	}
	
	@Deprecated
	public <T, E extends Exception> T debugGetThrow(
			TrySupplier<T, E> sup, Supplier<T> nullAlt) throws E {
		return debugCallDepthThrow(()-> getThrow(sup, nullAlt));
	}
	
	@Deprecated
	public boolean debugTests(Supplier<Boolean> target) {
		return debugCallDepth((SystemElement) this,
				()-> tests(target));
	}
	
    @Deprecated
	public <T> T debugTestsSkipNull(
            Boolean tester, Supplier<T> trueResult, Supplier<T> falseResult) {
        return debugCallDepth((Supplier<T>) ()-> 
        testsSkipNull(tester, trueResult, falseResult));
    }
    
    
    
	@Deprecated
	public <T> void debugToString(T target) {
		debug(target, Object::toString);
	}
	
	
	
	@Deprecated
	public static <T> T throwReductionException() 
			throws UnsupportedOperationException {
		return throwTodoException("true reduction");
	}
	
	@Deprecated
	public static <T> T throwTodoException(Exception cause) {
		return throwTodoException(null, cause);
	}
	
	/**
	 * For all unforgettable todo's, which MUST be implemented before removing the DebugElement extension!
	 * 
	 * @param message
	 * @throws UnsupportedOperationException
	 */
	@Deprecated
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
	@Deprecated
	public static <T> T throwTodoException(String message, Exception cause) {
		if (message == null) message = "unhandled exception";
		
		try {
			Elemental.haltException();
			if (cause == null) cause = new UnsupportedOperationException(
					"Sorry and please contact the development team to finish this task:\n" + message + "?");
			Elemental.throwHaltableException(cause);
			
		} catch (UnsupportedOperationException e1) {
			throw e1;
		} catch (Exception e) {
			return null;	
		}
		return null;	
	}
	
}