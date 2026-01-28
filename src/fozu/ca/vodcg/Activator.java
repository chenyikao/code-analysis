package fozu.ca.vodcg;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jgit.api.Git;
import org.eclipse.jgit.api.errors.GitAPIException;
import org.eclipse.jgit.lib.Repository;
import org.eclipse.jgit.revwalk.RevCommit;
import org.eclipse.jgit.storage.file.FileRepositoryBuilder;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.Bundle;
import org.osgi.framework.BundleContext;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

import org.eclipse.core.resources.*;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.swt.widgets.Display;

/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends AbstractUIPlugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "fozu.ca"; //$NON-NLS-1$
    
	// The shared instance
	private static Activator plugin;
	private static Bundle bundle = Platform.getBundle(PLUGIN_ID);
	
	IResourceChangeListener listener = event -> {
	    try {
	        event.getDelta().accept((IResourceDelta delta) -> {
	            final IResource res = delta.getResource(), parent = res.getParent();
	            if ((res.getType() == IResource.FILE && "HEAD".equals(res.getName()) && ".git".equals(parent.getName())) ||
	                (res.getType() == IResource.FOLDER && "heads".equals(res.getName()) && "refs".equals(parent.getName()))) {

	                // schedule background processing
	                FileRepositoryBuilder builder = new FileRepositoryBuilder();
	                try (final Repository repo = builder
	                        .setGitDir(res.getType() == IResource.FILE ? parent.getLocation().toFile() : parent.getParent().getLocation().toFile())
	                        .readEnvironment()
	                        .findGitDir()
	                        .build();
	                    final Git git = new Git(repo)) {

	                    final IPath resPath = res.getProjectRelativePath();
	                    final RevCommit commit = git.log().call().iterator().next();
	                    final String commitId = commit.getName().substring(0, 7);
	                    final String outPath = resPath.toOSString() + commitId + ".smt2", 
	                            task = "Generating " + outPath;
	                    final File writable = bundle.getDataFile(outPath); // relative path inside plugin data area
	                    if (!writable.getParentFile().exists()) {
	                        writable.getParentFile().mkdirs();
	                    }
	                    
	                    final Job job = new Job(task) {
	                        protected IStatus run(IProgressMonitor monitor) {
	                            final VODCondGen condGen = VODCondGen.from(resPath, Display.getCurrent());
	                            try {
	                                condGen.setStart(monitor, task);
	                                
	                                PrintStream outFile = new PrintStream(new File(outPath));
	                                outFile.print(condGen.generateDiffConditionString(commit, repo));
	                                outFile.close();
	                                
	                            } catch (IOException e) {   // top level general debugging?
	                                e.printStackTrace();
	                                return Status.CANCEL_STATUS;
//                              DebugElement.throwTodoException(e);
	                            }
	                            condGen.done(null, "Condition generated!");
	                            return Status.OK_STATUS;
	                        }
	                    };
	                    job.schedule();
	                } catch (IOException | GitAPIException e1) {
                        e1.printStackTrace();
                        return false;
                    }
	            }
	            return true;
	        });
	    } catch (CoreException e) {
	        e.printStackTrace();
	    }
	};

	/**
	 * The constructor
	 */
	public Activator() {
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;

		// Register (e.g., in plugin start)
		ResourcesPlugin.getWorkspace().addResourceChangeListener(
		    listener, IResourceChangeEvent.POST_CHANGE);
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);

		// Unregister at shutdown:
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(listener);
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static Activator getDefault() {
		return plugin;
	}

	/**
	 * Returns an image descriptor for the image file at the given
	 * plug-in relative path
	 *
	 * @param path the path
	 * @return the image descriptor
	 */
	public static ImageDescriptor getImageDescriptor(String path) {
		return imageDescriptorFromPlugin(PLUGIN_ID, path);
	}
}
