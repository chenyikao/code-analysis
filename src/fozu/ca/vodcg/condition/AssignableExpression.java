package fozu.ca.vodcg.condition;

import java.util.NavigableSet;
import java.util.function.Supplier;

import org.eclipse.jdt.core.dom.Statement;

import fozu.ca.DebugElement;
import fozu.ca.Elemental;
import fozu.ca.vodcg.Assignable;
import fozu.ca.vodcg.AssignableElement;
import fozu.ca.vodcg.Assignment;
import fozu.ca.vodcg.ASTException;
import fozu.ca.vodcg.IncomparableException;
import fozu.ca.vodcg.ReenterException;
import fozu.ca.vodcg.SystemElement;
import fozu.ca.vodcg.condition.data.NumericExpression;
import fozu.ca.vodcg.parallel.OmpDirective;
import fozu.ca.vodcg.parallel.ThreadPrivatizable;

/**
 * Assignable arithmetic expression.
 * 
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("removal")
public interface AssignableExpression 
extends ArithmeticExpression, AssignableElement, ThreadPrivatizable {

	public default void guard(Runnable runnable) {
		try {
			getAssignable().guard(runnable);
			
		} catch (NullPointerException e) {
			SystemElement.throwTodoException(e);
		}
	}
	
	public default <T> T guard(Supplier<T> returnSupplier) {
		return guard(returnSupplier, ()-> null);
	}
	
	public default <T> T guard(Supplier<T> returnSupplier, 
			Supplier<T> reenterSupplier) {
//		return AssignableExpression.this.guard(returnSupplier, reenterSupplier, null);
		try {
			return getAssignable().guard(
					returnSupplier, 
					reenterSupplier);
			
		} catch (NullPointerException e) {
			final SystemElement se = (SystemElement) this;
//			return se.debugGet(()-> se.guard(
			return se.guard(
					returnSupplier, 
					reenterSupplier);
			
		} catch (ClassCastException e) {
			return SystemElement.throwTodoException(e);
		}
	}
	
//	default public <T> T guard(Supplier<T> returnSupplier, 
//			Supplier<T> reenterSupplier, Method callee) {
//		try {
//			return getAssignable().guard(
//					returnSupplier, 
//					reenterSupplier,
//					callee);
//			
//		} catch (NullPointerException e) {
//			final SystemElement se = (SystemElement) this;
//			return se.debugGet(()-> se.guard(
//					returnSupplier, 
//					reenterSupplier,
//					callee));
//			
//		} catch (ClassCastException e) {
//			return SystemElement.throwTodoException(e);
//		}
//	}

	
	
	public static <T> T getAsnNonNull(Supplier<T> sup) {
		return AssignableElement.getAsn(sup, null);
	}
	
	
	
	/**
	 * @return null if not assigned.
	 */
	public default Assignment getAssignment() {
		return Elemental.tests(isAssigned())
				? getAssignmentIf()
				: null;
	}

	/**
	 * Should be invoked only if assigned.
	 * @return null only if this is non-AST.
	 */
	default Assignment getAssignmentIf() {
		return AssignableElement.getAsn(()-> 
		getAssignable().getFirstAssignment());
	}
	
	
	
	public default void setAssigner(Expression rhs) {
//		if (Elemental.testsNot(isAssigned())) SystemElement.throwTodoException("inconsistent assignedness");
		if (rhs == null) setAssigned((Boolean) null);
		else setAssigned();
	}
	
//	public void setAssignment(Assignment asm);
	
	public default void setAssigned() {setAssigned(true);}
	public void setAssigned(Boolean isAssigned);
	
	public default void setAssigned(Expression rhs) {
		setAssigner(rhs);	//asm.setAssigned(this, rhs);
//		setAssigner(rhs.cloneReversion(getPrivatizingBlock(), getAssigned().getThreadRole(), null));	//asm.setAssigned(this, rhs);
		assert rhs != null;
//		if (asm == null) return;	// may be called before asm ready
//		setAssignment(asm);	
//		if (rhs instanceof AssignableExpression) ((AssignableExpression) rhs).setAssignment(asm);
	}
	
	public default boolean hasAssignable() {
		return getAssignable() != null;
	}
	
	public default boolean isLikelyAssigned() {
		return Elemental.tests(isAssigned());
	}
		
	@Override
	public default Boolean isAssigned() {
		return AssignableElement.getAsn(()-> getAssignable().isAssigned(),
				this::throwUnsupportedException);
	}
	
	/**
	 * @return true if this is an AST or non-AST argument.
	 */
	public default boolean isArgument() {
		return getAsnNonNull(()-> 
		getAssignable().isArgument());
	}
	
	@Override
	public default Boolean isConstant() {
		return getAsnNonNull(()-> 
		getAssignable().isConstant());
	}
	
	@Override
	public default boolean isFunctional() {
		return SystemElement.tests(getAsnNonNull(()-> 
		getAssignable().isFunctional()));
	}
	
	public default boolean isUnsigned() throws IncomparableException {
		return getAsnNonNull(()-> 
		getAssignable().isUnsigned());
	}
	
	/**
	 * @return true only possibly if it's type is numeric. 
	 */
	@Override
	public default Boolean isZero() 
			throws ASTException {
		if (getType().isNumeric()) {
			if (Elemental.tests(isAssigned())) {
				final Assignable<?> asn = getAssignable();
				if (asn != null && asn.selfAssigns()) {
					if (asn.isLoopIterator()) {
						final SystemElement lr = ExpressionRange.fromIteratorOf(
								asn.getEnclosingCanonicalLoop(), 
								asn.getRuntimeAddress(),
								asn.getCondGen()).toConstant();
						if (lr == null) return null;
						if (lr instanceof NumericExpression)
							return ((NumericExpression) lr).isZero();
						DebugElement.throwTodoException("unsupported loop iterator");
					}
					
					final Expression pAsnr = asn.previousAssigner();
					if (pAsnr == null) return null;	// non-initialized
					if (pAsnr instanceof NumericExpression)
						return ((NumericExpression) pAsnr).isZero();
					DebugElement.throwTodoException("unsupported assigner");
				}
				
				final Expression asnr = getAssigner();
				if (asnr == null) return null;	// non-initialized
				if (asnr instanceof NumericExpression)
					return ((NumericExpression) asnr).isZero();
				DebugElement.throwTodoException("unsupported assigner");
			}
		}
		return ArithmeticExpression.super.isZero();
	}
	
	/**
	 * Faster checking for constant variables.
	 * Non-assigned means unknown value and scale.
	 * 
	 * @see fozu.ca.condition.ArithmeticExpression#isPositive()
	 */
	@SuppressWarnings("unchecked")
	@Override
	public default Boolean isPositive() throws ReenterException {
		return trySkipNullException(
				getMethod(AssignableExpression.class, "isPositive"),
				// main return
				()-> getAssignable().isUnsigned(),
				((NumericExpression) getAssigner())::isPositive,
				ArithmeticExpression.super::isPositive);
	}
	
	/**
	 * Faster checking for constant variables.
	 * Non-assigned means unknown value and scale.
	 * 
	 * @fozu.caozu.ca.condition.ArithmeticExpression#isPositiveInfinity()
	 */
	@SuppressWarnings("unchecked")
	@Override
	public default Boolean isPositiveInfinity() throws ReenterException {
		return trySkipNullException(
				getMethod(AssignableExpression.class, "isPositiveInfinity"),
				// main return
				((NumericExpression) getAssigner())::isPositiveInfinity,
				ArithmeticExpression.super::isPositiveInfinity);
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public default boolean isPrivate() {
		try {
			return trySkipNullException(
					()-> isThreadPrivate(),
					()-> getAssignable().isThreadPrivate(),
					ArithmeticExpression.super::isPrivate);
			
		} catch (Exception e) {
			return SystemElement.throwTodoException(e);
		}
	}

	
	
	/**
	 * Faster checking for constant variables.
	 * Non-assigned means unknown value and scale.
	 * 
	 *fozu.ca fozu.ca.condition.ArithmeticExpression#isNegative()
	 */
	@SuppressWarnings("unchecked")
	@Override
	public default Boolean isNegative() throws ReenterException {
		return trySkipNullException(
				getMethod(AssignableExpression.class, "isNegative"),
				// main return
				()-> isSelfAssigned() ? ((NumericExpression) getAssigner()).isNegative() : null,
				ArithmeticExpression.super::isNegative);
	}
	
	/**
	 * Faster checking for constant variables.
	 * Non-assigned means unknown value and scale.
	 * 
	fozu.caee fozu.ca.condition.ArithmeticExpression#isNegativeInfinity()
	 */
	@SuppressWarnings("unchecked")
	@Override
	public default Boolean isNegativeInfinity() throws ReenterException {
		return trySkipNullException(
				getMethod(AssignableExpression.class, "isNegativeInfinity"),
				// main return
				((NumericExpression) getAssigner())::isNegativeInfinity,
				ArithmeticExpression.super::isNegativeInfinity);
	}
	
	
	
	@SuppressWarnings("unchecked")
	public default Boolean equals(AssignableExpression ae2) 
			throws ReenterException {
		if (ae2 == null) return SystemElement.throwNullArgumentException("assignable expression");
		return trySkipNullException(
				getMethod(AssignableExpression.class, "equals", AssignableExpression.class),
				// main return - initializer list elements share the same assignment but are not necessarily equal
				()-> getAssignment() != ae2.getAssignment() ? false : null,
				()-> ArithmeticExpression.super.equals(ae2));
	}

	
	
	/**
	 * @return non-null if the assignable exists
	 */
	public default NavigableSet<OmpDirective> getEnclosingDirectives() {
		return AssignableElement.getAsn(()-> 
		getAssignable().getEnclosingDirectives());
	}
	
	@Override
	public default Statement getPrivatizingBlock() {
		return AssignableElement.getAsn(()-> 
		getAssignable().getPrivatizingBlock());
	}
	
	@Override
	public default <T> T throwUnsupportedException() {
		return DebugElement.throwTodoException(
				"unsupported assignable expression");
	}
	
}