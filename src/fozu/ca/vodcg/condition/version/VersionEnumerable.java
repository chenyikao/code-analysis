/**
 * 
 */
package fozu.ca.vodcg.condition.version;

import java.util.Collections;
import java.util.List;
import java.util.NavigableSet;
import java.util.TreeSet;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Statement;

import fozu.ca.DebugElement;
import fozu.ca.Elemental;
import fozu.ca.vodcg.ASTAddressable;
import fozu.ca.vodcg.AssignableElement;
import fozu.ca.vodcg.VODCondGen;
import fozu.ca.vodcg.condition.Referenceable;
import fozu.ca.vodcg.condition.data.PlatformType;
import fozu.ca.vodcg.parallel.ThreadPrivatizable;

/**
 * @author Kao, Chen-yi
 *
 */
@SuppressWarnings("removal")
public interface VersionEnumerable<S extends Referenceable> 
extends ASTAddressable, AssignableElement, ThreadPrivatizable {

//	Set<Version<Variable>> getDirectVariableReferences();
	
	public Boolean isGlobal();
//	public Boolean isDirectlyFunctional();
	
	public default boolean isDeclarator() {
		return !isInAST()
				? DebugElement.throwInvalidityException("non-AST")
				: DebugElement.throwTodoException("unsupported declarator");
	}
	
	public default boolean isParameter() {
		return DebugElement.throwTodoException("unsupported parameter");
	}
	
	public default boolean isLoopIterator() {
		return isLoopIteratingIterator() || isLoopInitializedIterator();
	}
	
	public default boolean isLoopIteratingIterator() {
		return !isInAST()
				? DebugElement.throwInvalidityException("non-AST")
				: DebugElement.throwTodoException("unsupported loop iterator");
	}
	
	public default boolean isLoopInitializedIterator() {
		return !isInAST()
				? DebugElement.throwInvalidityException("non-AST")
				: DebugElement.throwTodoException("unsupported loop iterator");
	}
	
//	default public boolean testsAssigned() {
//		if (this instanceof Assignable) return Elemental.tests(((Assignable) this).isAssigned());
//		if (this instanceof AssignableExpression) return Elemental.tests(((AssignableExpression) this).isAssigned());
//		return DebugElement.throwTodoException("unsupported assignable");
//	}
	

	
	/**
	 * @return non-null
	 */
	@SuppressWarnings("unchecked")
	public default <T extends VersionEnumerable<S>> T previousOrUnambiguousAssigned() {
		if (Elemental.tests(isAssigned())) return (T) this;
		
		final NavigableSet<VersionEnumerable<S>> pras = previousRuntimeAssigneds();
		return pras.isEmpty()
				? Elemental.get(()-> previous(), ()-> (T) this)
				: (T) pras.first();
	}
	
	/**
	 * @param <T>
	 * @return non-null
	 */
	public default <T extends VersionEnumerable<S>> NavigableSet<T> previousRuntimeAssigneds() {
		final NavigableSet<T> prs = previousRuntimes();
		if (prs == null) return Collections.emptyNavigableSet();
		
		NavigableSet<T> pras = new TreeSet<>(prs);
		for (T pr : prs) 
			if (!Elemental.tests(pr.isAssigned())) pras.remove(pr);

		// previous runtimes' previousRuntimeAssigneds()
		if (pras.isEmpty()) for (T pr : prs) {
			pras = pr.previousRuntimeAssigneds();
			if (!pras.isEmpty()) break;
		}
		return pras;
	}

//	@Override
//	default public Assignable<?> getAssignable() {
//		return isInAST()
//				? AssignableElement.super.getAssignable()
//				: null;
//	}
	
	
	
	@Override
	public default ASTNode getASTAddress() {
		return AssignableElement.getAsn(()-> 
		getAssignable().getASTAddress());
	}
	
	@Override
	default String getShortAddress() {
		return isInAST()
				? ASTAddressable.super.getShortAddress()
				: getName();
	}
	
	public VODCondGen getCondGen();

//	public NavigableSet<OmpDirective> getEnclosingDirectives();
	public default List<Statement> getDependentLoops() {
		return Collections.emptyList();
	}
	
//	default public Subject getSubject() {
//		try {
//			return getVersion().getSubject();
//		} catch (ReenterException | IncomparableException | UncertainPlaceholderException | NoSuchVersionException e) {
//			return null;
//		}
//	}
	
	public String getName();
	public PlatformType getType();
	
	/**
	 * @return the indirect variable/function subject but not direct version reference.
	 * 	This is distinguished from {@link VersionPlaceholder#getSubject()}.
	 */
	public default S getVersionSubject() {
		return getVersion().getSubject();
	}
	
	/**
	 * @return the current version with initialization or reversion,
	 * 	therefore it may <em>not</em> be null.
	 */
	public default Version<S> getVersion() {
		return Elemental.get(this::peekVersion,
				()-> DebugElement.throwTodoException("unsupported operation"));
	}
	public default Version<S> getVersion(FunctionallableRole role) {
		return Elemental.get(()-> peekVersion(role),
				()-> DebugElement.throwTodoException("unsupported operation"));
	}
	
	/**
	 * @return the current version without initialization nor reversion,
	 * 	therefore it may be null.
	 */
	public Version<S> peekVersion();
	public default Version<S> peekVersion(ThreadRoleMatchable role) {
		return role == null
				? null
				: DebugElement.throwTodoException("unsupported role");
	}
	
	/**
	 * Replacing current version without checking inter-version compliance.
	 * @param newVersion
	 * @throws NoSuchVersionException 
	 */
	public default void setVersion(Version<? extends S> newVersion) throws NoSuchVersionException {
		DebugElement.throwTodoException("unsupported operation");
	}
	
	public default boolean reversions() {
		return !Elemental.testsNot(isAssigned());	// null or isAssigned
	}
	
	public default void reversion(Version<? extends S> newVersion) throws NoSuchVersionException {
		if (!reversions()) DebugElement.throwTodoException("in-reversionable VersionEnumerable");
	}

}