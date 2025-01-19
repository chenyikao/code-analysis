/**
 * 
 */
package fozu.ca.vodcg;

import java.io.IOException;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jface.text.ITextSelection;

import fozu.ca.vodcg.util.ASTNameFinder;
import fozu.ca.vodcg.util.ASTUtil;

/**
 * Path to locate a variable in plain source code (not indexed model).
 *  
 * @author Kao, Chen-yi
 *
 */
public class VariablePath {

	private static final IllegalArgumentException ILLEGAL_VP_EXCEPTION = 
			new IllegalArgumentException("Must provide a variable and its path!");
	
	private Assignable<?> lv;
	private int line;
	private IPath filePath;
	
	
	
//	private VariablePath(String varName, int varLine, IPath filePath, VOPCondGen condGen) 
//			throws CModelException, CoreException, InterruptedException {
//		if (varName == null || filePath == null) throw ILLEGAL_VP_EXCEPTION;
//		else set(varName, varLine, filePath, condGen);
//	}
	
	private VariablePath(Assignable<?> varLv, int varLine, IPath filePath) {
		set(varLv, varLine, filePath);
	}
	
	/**
	 * @param tvPath - the path to target variable in syntax <var:line@project/folder/file.c>
	 * @param condGen 
	 * @throws NumberFormatException 
	 * @throws IOException 
	 * @throws ASTException 
	 */
	public VariablePath(String tvPath, VODCondGen condGen) throws NumberFormatException, ASTException, IOException {
		final String[] tvpStruct = tvPath.split("[:@]");
		if (tvpStruct.length == 3) 
			set(tvpStruct[0], Integer.parseInt(tvpStruct[1]), new Path(tvpStruct[2]), condGen);
		else throw ILLEGAL_VP_EXCEPTION;
	}

	public static VariablePath from(
			ITextSelection selection, IPath filePath, VODCondGen condGen) {
		// Loading C-Index AST
//		final IIndex index = CCorePlugin.getIndexManager().getIndex(projs);	// findReferences(...) doesn't work!
//		while (true) {
//		try {
//			index.acquireReadLock(); // we need a read-lock on the index
//		} catch (InterruptedException e) {
//			continue;
//		} finally {
//			index.releaseReadLock();
//		}
//		}
			
		final Name varName = ASTUtil.getNameFrom(
				filePath, selection.getOffset(), selection.getLength(), true);
		if (varName != null) return new VariablePath(
				Assignable.from(varName, null, condGen), 
				ASTUtil.getAST(filePath).getLineNumber(varName.getStartPosition()), 
				filePath);
		else return null;
			
	}
	


	public Assignable<?> getLValue() {
		return lv;
	}
	
	public Name getName() {
		return lv.getASTName();
	}
	
	public int getLine() {
		return line;
	}
	
	public IPath getFilePath() {
		return filePath;
	}



	private void set(Assignable<?> varLv, int varLine, IPath filePath) {
		if (varLv == null || varLine < 0 || filePath == null) 
			throw new IllegalArgumentException("Invalid variable path!");
//		if (var_name.getBinding() == null) set(var_name.getLastName().toString(), var_line, file_path);
//		else {
			lv = varLv;
			line = varLine;
			this.filePath = filePath;
//		}
	}
	
	private void set(String varName, int varLine, IPath filePath, VODCondGen condGen) throws ASTException, IOException {
	    this.line = varLine;
		this.filePath = filePath;
		this.lv = Assignable.from(new ASTNameFinder(filePath).find(varName, varLine), null, condGen);
	}

	
	
	public String toString() {
		return lv.toASTExpression() + ":" + line + "@" + filePath.toPortableString();
	}
	
}