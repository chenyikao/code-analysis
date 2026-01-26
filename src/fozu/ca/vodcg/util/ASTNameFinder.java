/**
 * 
 */
package fozu.ca.vodcg.util;

import java.io.IOException;

import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.Name;

/**
 * @author Kao, Chen-yi (Timmy)
 * 
 */
public class ASTNameFinder extends ASTVisitor {

    private final CompilationUnit compilationUnit;
    private String name;
    private int lineNumber;
    private Name nameNode = null;
    
    public ASTNameFinder(final IPath filePath) throws IOException {
        compilationUnit = ASTUtil.getAST(filePath);
    }

    public ASTNameFinder(final IPath filePath, int offset, int length) throws IOException {
        compilationUnit = ASTUtil.getAST(filePath, offset, length);
    }
    
    public Name find() {
        compilationUnit.accept(this);
        return nameNode;
    }
    
    public Name find(final String fullyQualifiedName, final int lineNumber) {
        this.name = fullyQualifiedName;
        this.lineNumber = lineNumber;
        compilationUnit.accept(this);
        return nameNode;
    }

    @Override
    public boolean preVisit2(ASTNode node) {
        if (node instanceof Name) {
            final Name nameNode = (Name) node;
            if (name == null) {
                this.nameNode = nameNode;
            } else if (nameNode.getFullyQualifiedName().equals(name)
                    && lineNumber == compilationUnit.getLineNumber(node.getStartPosition())) {
                this.nameNode = nameNode;
            }
        }
        return nameNode == null;
    }
    
}