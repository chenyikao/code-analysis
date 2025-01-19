/**
 * 
 */
package fozu.ca.vodcg.util;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.Name;

/**
 * @author Kao, Chen-yi (Timmy)
 * 
 */
public class ASTNameCollector extends ASTVisitor {

    private final String name;
    private final List<Name> names = new ArrayList<>();
    
    public ASTNameCollector(String fullyQualifiedName) {
        name = fullyQualifiedName;
    }

    public List<Name> getNames() {
        return names;
    }

    @Override
    public boolean preVisit2(ASTNode node) {
        if (node instanceof Name) {
            final Name nameNode = (Name) node;
            if (nameNode.getFullyQualifiedName().equals(name)) names.add(nameNode);
            return false;
        }
        return true;
    }
    
}