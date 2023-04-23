package fozu.ca.vodcg.condition.version;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.function.Supplier;

import fozu.ca.DebugElement;
import fozu.ca.Elemental;
import fozu.ca.vodcg.SystemElement;
import fozu.ca.vodcg.condition.ArithmeticExpression;
import fozu.ca.vodcg.condition.Expression;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("removal")
public interface ThreadRoleMatchable {

	public Boolean isConstant();
	
	/**
	 * @return 
	 * @throws unknown exception even if this is either private or shared.
	 * 	isPrivate - thread-private non-array locals are not functional;
	 * 	isShared - shared non-arrays or arrays without loops/pragmas are not functional.
	 */
	public default boolean isFunctional() {
		if (SystemElement.tests(isConstant())) return false;
		return getNonNullThis(()-> getThreadRole().isFunctional());
	}
	
	public default boolean isPrivate() {
		return getNonNullThis(this::getThreadRole).isPrivate();
	}
	
	public default boolean isShared() {
		return !isPrivate();
	}
	
	public default <T> T getNonNullThis(Supplier<T> sup) {
		final T result = Elemental.getNonNull(sup);
		return result == this
				? throwUnsupportedRoleException()
				: result;
	}

	public default FunctionallableRole getThreadRole() {
		return Elemental.tests(isConstant())
				? ThreadRole.CONST
				: ThreadRole.MASTER;
//				: throwUnsupportedRoleException();
	}
	
	/**
	 * @param exps - including possibly null expression elements.
	 * @return
	 */
	public static FunctionallableRole getThreadRole(Collection<? extends Expression> exps) {
		if (exps == null) return null;
		
		FunctionallableRole role = null;
		for (Expression e : exps) {
			if (e == null) continue;
			final FunctionallableRole eRole = 
					e.guard(e::getThreadRole, ()-> ThreadRole.MASTER);
			if (role == null || role.derives(eRole)) role = eRole;
		}
		return role;
	}
	
	/**
	 * @param exps - including possibly null expression arguments.
	 * @return
	 */
	public static FunctionallableRole getThreadRole(Expression... exps) {
		if (exps == null) return null;
		return getThreadRole(Arrays.asList(exps));
	}
	
	public static FunctionallableRole getThreadRole(ArithmeticExpression... exps) {
		if (exps == null) return null;
		final Collection<Expression> es = new ArrayList<>();
		for (ArithmeticExpression e : exps) {
			if (e == null) continue;
			if (e instanceof Expression) es.add((Expression) e);
			else DebugElement.throwTodoException("unsuported arithmetic exception");
		}
		return getThreadRole(es);
	}
	

	
	/**
	 * @param exps - including possibly null expression arguments.
	 * @return
	 */
	public default ThreadRoleMatchable derive(Expression... exps) {
		return derive(null, exps);
	}
	
	public default ThreadRoleMatchable derive(ThreadRoleMatchable matchable2, Expression... exps) {
		final FunctionallableRole eRole = getThreadRole(exps);
		final Boolean dm2 = matchable2 == null ? null : derives(matchable2);
		final Boolean der = eRole == null ? null : derives(eRole);
		if (dm2 == null) {
			if (der == null) return this;
			if (der) return eRole;
		} else if (dm2) {
			if (der == null) return matchable2;
			if (der) {
				if (matchable2.derives(eRole)) return eRole;
				return matchable2;
			}
		}
		return DebugElement.throwTodoException("inderivable roles");
	}
	
	/**
	 * @param matchable2
	 * @return true for every constants and race-version-derivable's.
	 * 	Otherwise return match-based derive-ness.
	 */
	public default boolean derives(ThreadRoleMatchable matchable2) {
		if (SystemElement.tests(isConstant()) 
				|| matchable2 instanceof RaceVersion) return true;
		return matchable2 instanceof Version
				? matches(((Version<?>) matchable2).getThreadRole())
				: matches(matchable2);
	}
	
	public default boolean matches(ThreadRoleMatchable matchable2) {
		return equals(matchable2);
	}

	/**
	 * Override-able instance method for sub-classing.
	 * 
	 * @param <T>
	 * @return
	 */
	public default <T> T throwUnsupportedRoleException() {
		return DebugElement.throwTodoException("unsupported role type");
	}
	
}