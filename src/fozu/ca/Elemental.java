/**
 * 
 */
package fozu.ca;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.BooleanSupplier;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.function.UnaryOperator;

import fozu.ca.vodcg.util.ASTAssignableComputer;

/**
 * Providing all static general utility methods for other specific utility classes like {@link ASTAssignableComputer}, etc.
 * 
 * @author Kao, Chen-yi
 *
 */
public abstract class Elemental {

	public static interface TryRunnable {
		void run() throws Exception;
		
		default Runnable toRunnable(final List<Exception> nonSkips,
				@SuppressWarnings("unchecked") final Class<? extends Exception>... skips) {
			return ()-> {try {
				run();
			} catch (Exception e) {
				if (skips != null) 
					for (Class<? extends Exception> skip : skips) 
						if (skip.isInstance(e)) return;
				if (nonSkips == null) throwUnhandledException(e);
				nonSkips.add(e);
			}};
		}
	}
	
	
	
	public static interface TrySupplier<T, E extends Exception> {
		T get() throws E;
		
		default Supplier<T> toSupplier(final List<E> nonSkips, 
				@SuppressWarnings("unchecked") final Class<? extends Exception>... skips) {
			return toSupplier(nonSkips, Arrays.asList(skips));
		}
		
		/**
		 * @param nonSkips - for storing non-skipped exceptions to re-throw after executing the non-throwing Java supplier.
		 * 	Can be null provided all skipped exceptions registered via {@code skips}.
		 * @param skips
		 * @return
		 */
		@SuppressWarnings("unchecked")
		default Supplier<T> toSupplier(
				final List<E> nonSkips, final List<Class<? extends Exception>> skips) {
			return ()-> {try {
				return get();
			} catch (Exception e) {
				if (skips != null) 
					for (Class<? extends Exception> skip : skips) 
						if (skip.isInstance(e)) return null;
				
				if (nonSkips == null) throwUnhandledException(e);
				try {nonSkips.add((E) e);}
				catch (ClassCastException e2) {throwUnhandledException(e2);}
				return null;
			}};
		}
	}
	
	
	
	public static interface TryFunction<T, R> {
		R apply(T input) throws Exception;
		
		default Function<T, R> toFunction(
				@SuppressWarnings("unchecked") final Class<? extends Exception>... skips) {
			return toFunction(null, skips);
		}
		
		default Function<T, R> toFunction(
				final List<Exception> nonSkips, 
				@SuppressWarnings("unchecked") final Class<? extends Exception>... skips) {
			return input_-> {try {
				return apply(input_);
			} catch (Exception e) {
				if (skips != null) 
					for (Class<? extends Exception> skip : skips) 
						if (skip.isInstance(e)) return null;
				if (nonSkips == null) throwUnhandledException(e);
				nonSkips.add(e);
				return null;
			}};
		}
	}
	

	
	@SafeVarargs
	public static void run(final Runnable r, final Supplier<Boolean>... conjTesters) {
		if (!testsNot(testsSkipNullException(conjTesters))) r.run(); 
	}
	
	public static void runSkipNull(final Runnable r) {
		try {
			r.run();
		} catch (NullPointerException e) {
		} catch (Exception e) {
		    throwUnhandledException(e);
		}
	}
	
	public static void runSkipException(final Runnable r) {
		try {
			r.run();
		} catch (Exception e) {
		}
	}
	
	public static <T, U, R> R apply(
			BiFunction<T, U, R> func, Supplier<T> input1, Supplier<U> input2, Function<Exception, R> returnAlt) {
		return get(()-> func.apply(input1.get(), input2.get()), returnAlt);
	}
	
	@SafeVarargs
	public static <T, R> R apply(Function<T, R> func, Supplier<T> input, Supplier<R> returnAltNull, 
			Supplier<Boolean>... conjTesters) throws Exception {
		return apply(func, input, returnAltNull, null, conjTesters);
	}
	
	@SafeVarargs
	public static <T, R> R apply(Function<T, R> func, Supplier<T> input, Function<Exception, R> returnAlt, 
			Supplier<Boolean>... conjTesters) {
		return apply(func, input, ()-> returnAlt.apply(null), returnAlt, conjTesters);
	}
	
	@SafeVarargs
	public static <T, R> R apply(Function<T, R> func, Supplier<T> input, Supplier<R> returnAltNull, 
			Function<Exception, R> returnAltExc, Supplier<Boolean>... conjTesters) {
		if (input != null && func != null && !testsNot(testsSkipNullException(conjTesters))) try {
			final T in = input.get();
			if (in != null) {
				final R result = func.apply(in);
				if (result != null) return result;
			}
//		} catch (NullPointerException e) {	// including func == null || input == null
		} catch (Exception e) {	
			if (returnAltExc == null) throw e;
			return returnAltExc.apply(e);
		}
		return returnAltNull == null ? null : returnAltNull.get();
	}
	
	@SafeVarargs
	public static <T, R, E extends Exception> R apply(
			TryFunction<T, R> func, Supplier<T> input, TrySupplier<R, E> returnAltNull, 
			TryFunction<Exception, R> returnAltExc, Class<? extends Exception>... skips) {
		if (func == null) throwNullArgumentException("function");
		return apply(
				func.toFunction(skips), 
				input, 
				returnAltNull.toSupplier(null, skips), 
				returnAltExc.toFunction(skips));
	}
	
	public static String applySkipEmpty(UnaryOperator<String> func, Supplier<String> inputSup) 
					throws Exception {
		if (func == null) throwNullArgumentException("consumer");
		if (inputSup == null) throwNullArgumentException("input supplier");
		
		final String input = getSkipNull(inputSup);
		return input != null && !input.isBlank() ? func.apply(input) : "";
	}
	
	/**
	 * Applying {@code func} only if all testings result in true and {@code inputSup} results in non-null.
	 * @param <T>
	 * @param <R>
	 * @param func
	 * @param inputSup
	 * @param conjTesters
	 * @return
	 */
	@SafeVarargs
	public static <T extends Emptable, R> R applySkipEmpty(
			Function<T, R> func, Supplier<T> inputSup, Supplier<Boolean>... conjTesters) {
		if (func == null) throwNullArgumentException("consumer");
		if (inputSup == null) throwNullArgumentException("input supplier");
		
		if (testsNot(testsSkipNullException(conjTesters))) return null;
		
		T input = getSkipNull(inputSup);
		return input != null && !input.isEmpty() ? func.apply(input) : null;
	}
	
	@SuppressWarnings("unchecked")
	@SafeVarargs
	public static <C extends Collection<T>, T, R> R applySkipEmptyCol(
			Function<C, R> func, Supplier<C> inputSup, Supplier<Boolean>... conjTesters) {
		return applySkipEmpty(ec-> func.apply((C) ec.getKernel()), ()-> EmptableCollection.from(inputSup), conjTesters);
	}
	
	/**
	 * Applying {@code func} only if all testings result in true and {@code inputSup} results in non-null.
	 * @param <T>
	 * @param <R>
	 * @param func
	 * @param inputSup
	 * @param conjTesters
	 * @return
	 */
	@SafeVarargs
	public static <T, R> R applySkipNullException(
			Function<T, R> func, Supplier<T> inputSup, Supplier<Boolean>... conjTesters) {
		if (func == null) throwNullArgumentException("consumer");
		if (inputSup == null) throwNullArgumentException("input supplier");
		
		if (testsNot(testsSkipNullException(conjTesters))) return null;
		
		T input = getSkipException(inputSup);
		return input != null ? func.apply(input) : null;
	}
	
	/**
	 * Applying {@code func} only if all testings result in true and {@code inputSup} results in non-null.
	 * @param <T>
	 * @param <R>
	 * @param func
	 * @param inputSup
	 * @param conjTesters
	 * @return
	 */
	@SafeVarargs
	public static <T, R> R applySkipNull(
			Function<T, R> func, Supplier<T> inputSup, Supplier<Boolean>... conjTesters) {
		if (func == null) throwNullArgumentException("consumer");
		if (inputSup == null) throwNullArgumentException("input supplier");
		
		if (testsNot(testsSkipNullException(conjTesters))) return null;
		
		T input = getSkipNull(inputSup);
		return input != null ? func.apply(input) : null;
	}
	
	@SafeVarargs
	public static <T, R> R applySkipNull(
			TryFunction<T, R> func, Supplier<T> inputSup, Class<? extends Exception>... skips) 
					throws Exception {
		final List<Exception> nonSkips = new ArrayList<>();
		final R result = applySkipNull(func.toFunction(nonSkips, skips), inputSup);
		if (!nonSkips.isEmpty()) throw nonSkips.get(0);
		return result;
	}
	
	/**
	 * Applying {@code func} only if all testings result in true and {@code inputSup} results in non-null.
	 * @param <T>
	 * @param <R>
	 * @param func
	 * @param inputSup
	 * @param nnpeFunc - a non-null-pointer exception handler
	 * @param conjTesters
	 * @return
	 */
	@SafeVarargs
	public static <T, R> R applySkipNull(
			Function<T, R> func, Supplier<T> inputSup, Function<Exception, R> nnpeFunc, Supplier<Boolean>... conjTesters) {
		try {
			return applySkipNull(func, inputSup, conjTesters);
			
		} catch (Exception e) {
			return nnpeFunc == null
					? throwUnhandledException(e)
					: nnpeFunc.apply(e);
		}
	}
	

	
	public static <T> boolean add(
			Collection<T> col, T ele, List<Class<? extends Exception>> skips) 
					throws Exception {
		return add(col, (Supplier<T>) ()-> ele, skips);
	}
	
	public static <T> boolean add(
			Collection<T> col, Supplier<T> eleSup, List<Class<? extends Exception>> skips) 
					throws Exception {
		return add(col, eleSup, null, skips);
	}
	
	@SafeVarargs
	public static <T> boolean add(
			final Collection<T> col, final Supplier<T> eleSup, final Supplier<Boolean> nullAlt, 
			final List<Class<? extends Exception>> skips, final Supplier<Boolean>... conjTesters) 
					throws Exception {
		if (col == null) return false;
		try {
			return apply(ele-> !col.contains(ele) && col.add(ele), 
					eleSup, 
					nullAlt != null ? nullAlt : ()-> false, 
					conjTesters);
			
		} catch (Exception e) {
			if (skips != null) 
			    for (Class<? extends Exception> skip : skips) 
			        if (skip.isInstance(e)) return false;
			return throwUnhandledException(e);
		}
	}
	
	@SafeVarargs
	public static <T> boolean addNonNull(Collection<T> col, 
			Supplier<T> eleSup, String exception, Supplier<Boolean>... conjTesters) 
					throws Exception {
		if (col == null) throwNullArgumentException("collection");
		if (!addSkipNull(col, eleSup, null, conjTesters)) throwNullArgumentException(exception);
		return true;
	}
	
	/**
	 * Skipping null elements but not excpetions.
	 * 
	 * @param <T>
	 * @param col
	 * @param eleSup
	 * @return
	 * @throws Exception
	 */
	public static <T> boolean addSkipNull(
			Collection<T> col, Supplier<T> eleSup) 
					throws Exception {
		return addSkipNull(
				col, 
				eleSup, 
				Arrays.asList(NullPointerException.class));
	}
	
//	static public <T> boolean addSkipNull(Collection<T> col, Supplier<T> eleSup, 
//			List<Class<? extends Exception>> skips) throws Exception {
//		return addSkipNull(col, eleSup, null, skips);
//	}
	
	@SafeVarargs
	public static <T> boolean addSkipNull(
			Collection<T> col, Supplier<T> eleSup, 
			List<Class<? extends Exception>> skips, 
			Supplier<Boolean>... conjTesters) 
					throws Exception {
		if (col == null) return false;
		try {
			return applySkipNull(
					ele-> !col.contains(ele) && col.add(ele), 
					eleSup, 
					conjTesters);
				
		} catch (Exception e) {
			if (skips != null) 
			    for (Class<? extends Exception> s : skips) 
			        if (s.isInstance(e)) return false;
			throw e;
		}
	}
	
	@SafeVarargs
	public static <T> boolean addAllNonNull(Collection<T> col, 
			Supplier<Collection<? extends T>> col2Sup, String exception, 
			Supplier<Boolean>... conjTesters) throws IllegalArgumentException, Exception {
		if (col == null) throwNullArgumentException("collection");
		if (!addAllSkipNull(col, col2Sup, conjTesters)) throwNullArgumentException(exception);
		return true;
	}
	
	public static <T> boolean addAllSkipException(Collection<T> col, 
			Supplier<Collection<? extends T>> col2Sup) {
		if (col == null || col2Sup == null) return false;
		try {
			return col.addAll(col2Sup.get());
		} catch (Exception e) {
			return false;
		}
	}
	
	@SafeVarargs
	public static <T> boolean addAllSkipNull(Collection<T> col, 
			Supplier<Collection<? extends T>> col2Sup, 
			Supplier<Boolean>... conjTesters) {
		if (col == null) return false;
		return get( 
				()-> applySkipNull(col::addAll, col2Sup, conjTesters),
				e-> false);
	}
	
	@SafeVarargs
	public static <T> void consume(Consumer<T> con, Supplier<T> input, Consumer<Exception> conAlt, 
			Supplier<Boolean>... conjTesters) {
		apply(	t-> {con.accept(t); return null;}, 
				input, 
				null, 	// Consumers always return null
				e-> {conAlt.accept(e); return null;}, 
				conjTesters);
	}
	
	@SafeVarargs
	public static <T extends Emptable> void consumeAltEmpty(
			Consumer<T> con, Supplier<T> inputSup, Runnable runAltEmpty, Supplier<Boolean>... conjTesters) 
					throws Exception {
		apply(input-> {if (!input.isEmpty()) con.accept(input); return null;}, 
				inputSup,
				()-> {runAltEmpty.run(); return null;},
				conjTesters);
	}
	
	@SafeVarargs
	public static <T> void consumeNonNull(
			final Consumer<T> con, final T input, Supplier<Boolean>... conjTesters) {
		if (con == null) throwNullArgumentException("consumer");
		if (input == null) throwNullArgumentException("input");
		
		if (!tests(testsSkipNullException(conjTesters))) return;
		
		con.accept(input);
	}

	/**
	 * @param <T>
	 * @param con
	 * @param inputSup
	 * @param conjTesters - passing only if tested non-null
	 * @throws Exception 
	 */
	@SafeVarargs
	public static <T> void consumeNonNull(
			final Consumer<T> con, final Supplier<T> inputSup, Supplier<Boolean>... conjTesters) throws Exception {
		if (inputSup == null) throwNullArgumentException("input supplier");
		
		if (!tests(testsSkipNullException(conjTesters))) return;
		
		consumeNonNull(con, getSkipNull(inputSup), conjTesters);
	}
	
	/**
	 * @param <T>
	 * @param con
	 * @param inputSup
	 * @param conjTesters - passing only if tested non-null
	 * @throws E 
	 * @throws Exception 
	 */
	@SafeVarargs
	public static <T, E extends Exception> void consumeNonNull(
			final Consumer<T> con, final TrySupplier<T, E> inputSup, Supplier<Boolean>... conjTesters) 
					throws E {
		if (inputSup == null) throwNullArgumentException("input supplier");
		
		if (!tests(testsSkipNullException(conjTesters))) return;
		
		consumeNonNull(con, getThrow(inputSup, null), conjTesters);
	}
	
	@SafeVarargs
	public static <T> void consumeSkipNull(
			Consumer<T> con, Supplier<T> inputSup, Supplier<Boolean>... conjTesters) {
		applySkipNull(
				input-> {con.accept(input); return null;}, 
				inputSup, 
				conjTesters);
	}
	
	@SafeVarargs
	public static <T extends Emptable> void consumeSkipEmpty(
			Consumer<T> con, Supplier<T> inputSup, Supplier<Boolean>... conjTesters) throws Exception {
		applySkipEmpty(
				input-> {con.accept(input); return null;}, 
				inputSup, 
				conjTesters);
	}
	
	@SuppressWarnings("unchecked")
	@SafeVarargs
	public static <T extends Collection<?>, ET extends Emptable> void consumeSkipEmptyCol(
			Consumer<ET> con, Supplier<T> inputSup, Supplier<Boolean>... conjTesters) throws Exception {
		if (inputSup == null) return;
		final Collection<?> input = inputSup.get();
		if (input == null) return;
		applySkipEmpty(
				einput-> {con.accept((ET) einput); return null;}, 
				()-> Emptable.from(input), 
				conjTesters);
	}
	
	@SafeVarargs
	public static <T> void consumeSkipNullException(
			Consumer<T> con, Supplier<T> inputSup, Supplier<Boolean>... conjTesters) {
		applySkipNullException(
				input-> {con.accept(input); return null;}, 
				inputSup, 
				conjTesters);
	}
	
	
	
	public static <T> T get(Supplier<T> sup, Supplier<T> nullAlt) {
		return get(sup, nullAlt, null);
	}
	
	public static <T> T get(Supplier<T> sup, Function<Exception, T> alt) {
		if (alt == null) throwNullArgumentException("null-or-exception handler");
		return get(sup, ()-> alt.apply(null), alt);
	}
	
	/**
	 * @param <T>
	 * @param sup
	 * @param nullAlt - is used when either <code>sup.get()</code> returns null 
	 * 	or a NullPointerException thrown directly or indirectly from down under.
	 * @param nonNullExcAlt
	 * @return
	 */
	public static <T> T get(Supplier<T> sup, 
			Supplier<T> nullAlt, Function<Exception, T> nonNullExcAlt) {
		try {
			T result = sup.get();
			if (result != null) return result;
			
		} catch (NullPointerException e) {	// may NOT be thrown directly from sup
		} catch (Exception e) {				// non-null exception with conditional halting
//			if (nonNullExcAlt == null) throw e; 
//			return nonNullExcAlt.apply(e);
			return nonNullExcAlt == null 
					? throwUnhandledException(e) 
					: nonNullExcAlt.apply(e);
		}
		return nullAlt == null ? null : nullAlt.get();
	}
	
//	public static <T> T getAltException(Supplier<T> sup, Function<Exception, T> excAlt) {
//		try {
//			return get(sup);
//			
//		} catch (Exception e) {
//			return excAlt == null 
//					? DebugElement.throwUnhandledException(e) 
//					: excAlt.apply(e);
//		}
//	}

	public static <T> T getNonException(Supplier<T> sup) {
		try {
			return sup.get();
		} catch (Exception e) {
			throwUnhandledException(e);
		}
		return null;
	}
	
	/**
	 * Exceptions are conditionally passed and should be handled during DebugElement.throwHaltableException(e).
	 * @param <T>
	 * @param sup
	 * @return
	 */
	public static <T> T getNonNull(Supplier<T> sup) {
		return get(sup, ()-> throwInvalidityException("null supplier or result"));
	}
	
	public static <T> T getNonNullSupplier(Supplier<T> sup) {
		if (sup == null) throwNullArgumentException("supplier");
		return sup.get();
	}
	
	public static <T> T getSkipNull(Supplier<T> sup) {
		return get(sup, ()-> null, Elemental::throwUnhandledException);
	}
	
	@SafeVarargs
	public static <T, E extends Exception> T getSkipNull(
			TrySupplier<T, E> sup, Class<? extends Exception>... skips) throws E {
		final List<E> nonSkips = new ArrayList<>();
		final T result = get(sup.toSupplier(nonSkips, skips), ()-> null, null);
		if (!nonSkips.isEmpty()) throw nonSkips.get(0);
		return result;
	}
	
	@SuppressWarnings("unchecked")
	public static <T, E extends Exception> T getSkipNull(
			TrySupplier<T, E> sup, Function<E, T> execAlt, Class<? extends Exception>... skips) {
		try {
			return getSkipNull(sup, skips);
			
		} catch (Exception e) {
			if (execAlt == null) throwNullArgumentException("exception handler");
			return execAlt.apply((E) e);
		}
	}
	
	public static <T> T getSkipEmpty(Function<Collection<T>, T> func, Supplier<Collection<T>> sup) {
		return applySkipEmptyCol(func, sup);
	}
	
	public static <T> T getSkipException(Supplier<T> sup) {
		return get(sup, e-> null);
	}
	
	
	
	public static <T, E extends Exception> T getTry(TrySupplier<T, E> sup, Function<Exception, T> alt) {
		try {
			return getThrow(sup);
		
		} catch (Exception e) {
			if (alt == null) throwNullArgumentException("alternative");
			return alt.apply(e);
		}
	}
	
	public static <T, E extends Exception> T getThrow(TrySupplier<T, E> sup) throws E {
		return getThrow(sup, null);
	}
	
	/**
	 * @param <T>
	 * @param sup
	 * @param nullAlt - called even for NullPointerException
	 * @return
	 * @throws Exception
	 */
	public static <T, E extends Exception> T getThrow(
			TrySupplier<T, E> sup, Supplier<T> nullAlt) throws E {
		if (sup == null) throwNullArgumentException("supplier");
		return getThrow(sup, nullAlt, NullPointerException.class);
	}
	
	@SafeVarargs
	public static <T, E extends Exception> T getThrow(TrySupplier<T, E> sup, 
			Supplier<T> nullAlt, Class<? extends Exception>... skips) 
					throws E {
		final List<E> nonSkips = new ArrayList<>();
		final T result = get(
				sup.toSupplier(nonSkips, skips), nullAlt, null);
		if (!nonSkips.isEmpty()) throw nonSkips.get(0);
		return result;
	}
	
	/**
	 * @param <T>
	 * @param <E>
	 * @param sup
	 * @param nullAlt
	 * @return
	 * @throws E
	 * 	from nullAlt given any null result.
	 */
	public static <T, E extends Exception> T getNullThrow(
			TrySupplier<T, E> sup, TrySupplier<T, E> nullAlt) throws E {
		final T result = Elemental.getSkipNull(sup);
		return result == null ? nullAlt.get() : result;
	}

	
	
	@SafeVarargs
	static Boolean tests(
			boolean isConjunctive, Function<Supplier<Boolean>, Boolean> testerResolver, Supplier<Boolean>... testers) {
		if (testerResolver == null) return false;
		
		Boolean result = null;
		if (testers != null && testers.length > 0) for (Supplier<Boolean> sup : testers) {
			result = testerResolver.apply(sup);
			if (result != null && 
					((isConjunctive && !result) || (!isConjunctive && result))) 
				break;
		}
		return result;
	}
	
	public static boolean tests(Boolean tester) {
		return tester != null && tester;
	}
	
	public static boolean tests(Supplier<Boolean> tester) {
		return get(tester, ()-> false, e-> false);	// the null testing including NullPointerException
	}
	
	public static boolean tests(Supplier<Boolean> tester, Supplier<Boolean> nullTester) {
		return get(tester, nullTester, null);	// the null testing including NullPointerException
	}
	
	public static boolean testsNot(Boolean tester) {
		return tester != null && !tester;
	}
	
	public static boolean testsNot(Supplier<Boolean> tester) {
		return !get(tester, ()-> false, e-> false);	// the null testing including NullPointerException
	}
	
	public static boolean testsNonNull(Supplier<Boolean> tester) {
		return getNonNull(tester);
	}
	
	@SafeVarargs
	public static Boolean testsSkipNull(Supplier<Boolean>... conjTesters) {
		return tests(true, Elemental::getSkipNull, conjTesters);	
	}
	
	public static <T> boolean testsSkipNull(Function<T, Boolean> tester, Supplier<T> tSup) {
		if (tester == null) throwNullArgumentException("tester");
		if (tSup == null) throwNullArgumentException("supplier");
		final T t = tSup.get();
		return t != null && tester.apply(t);
	}
	
	public static <T> T testsSkipNull(Boolean tester, Supplier<T> trueResult, Supplier<T> falseResult) {
		if (tester == null) return null;
		if (trueResult == null || falseResult == null) throwNullArgumentException("supplier");
		return tester ? trueResult.get() : falseResult.get();
	}
	
	@SafeVarargs
	public static Boolean testsSkipNullException(Supplier<Boolean>... conjTesters) {
		try {
			return tests(true, tester-> get(tester, e-> null), conjTesters);
			
		} catch (Exception e) {
			return null;
		}
	}
	
	@SafeVarargs
	public static Boolean testsAnySkipNull(Supplier<Boolean>... disjTesters) {
		return tests(false, Elemental::getSkipNull, disjTesters);
	}
	
	/**
	 * @param disjTesters
	 * @return the first testing true if there is, or false if once tested, or null.
	 */
	@SafeVarargs
	public static Boolean testsFirst(BooleanSupplier... disjTesters) {
		boolean result = false;
		if (disjTesters != null && disjTesters.length > 0) 
			for (BooleanSupplier sup : disjTesters) {
			    result = sup.getAsBoolean();
			    if (result) break;
			}
		return result;
	}
	
	@SafeVarargs
	public static Boolean testsAnySkipNullException(Supplier<Boolean>... disjTesters) {
		try {
			return tests(
					false, 
					Elemental::getSkipException, 
					disjTesters);
			
		} catch (Exception e) {
			return null;
		}
	}
	
	@SafeVarargs
	public static <T> List<T> toList(T... array) {
		return array == null || array.length == 0 
				? Collections.emptyList() 
				: Arrays.asList(array);
	}
	
	/************************************************************
	 * The following exception creation methods are not removable
	 ************************************************************/
	
    private static boolean haltsException = false;

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
//      if (this instanceof SystemElement) ((SystemElement) this).clear();
    }
    
    public static <E extends Throwable, T> T throwHaltableException(E e) 
            throws E {
        if (e == null) throwNullArgumentException("exception");
//      final Throwable cause = e.getCause();
//      if (haltsException || (cause != null && cause.getCause() != null)) {
        if (haltsException) {
            e.printStackTrace();
            passException();
        }
        throw e;
    }
    
    public static <T> T throwIllegalStateException(String msg) 
            throws IllegalStateException {
        return throwHaltableException(new IllegalStateException(msg));
    }
    
    public static <T> T throwInvalidityException(String message) 
            throws IllegalArgumentException {
        return throwInvalidityException(message, null);
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
    
    public static <T> T throwNullArgumentException(String arg) {
        return throwNullArgumentException(arg, null);
    }
    
//  public static <T> T throwNullArgumentException(String arg, Supplier<T> returnAlt) {
//      return throwNullArgumentException(arg, null);
//  }
    
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
    
    public static <T> T throwUnhandledException(Exception source) {
        return throwInvalidityException("unhandled exception", source);
    }
    
}