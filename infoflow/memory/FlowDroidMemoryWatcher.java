package soot.jimple.infoflow.memory;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.jimple.infoflow.collect.ConcurrentHashSet;
import soot.jimple.infoflow.results.InfoflowResults;

import java.util.Set;

/**
 * FlowDroid's implementation of a handler for the memory warning system
 * 
 * @author Steven Arzt
 *
 */
public class FlowDroidMemoryWatcher {
	
    private final Logger logger = LoggerFactory.getLogger(getClass());
	private final MemoryWarningSystem warningSystem = new MemoryWarningSystem();
	
	private final Set<IMemoryBoundedSolver> solvers = new ConcurrentHashSet<>();
	private final InfoflowResults results;
	
	/**
	 * Creates a new instance of the {@link FlowDroidMemoryWatcher} class
	 */
	public FlowDroidMemoryWatcher() {
		this(null);
	}
	
	/**
	 * Creates a new instance of the {@link FlowDroidMemoryWatcher} class
	 * @param res The result object in which to register any abortions
	 */
	public FlowDroidMemoryWatcher(InfoflowResults res) {
		// Register ourselves in the warning system
//		warningSystem.addListener(new OnMemoryThresholdReached() {
//
//			@Override
//			public void onThresholdReached(long usedMemory, long maxMemory) {
//				// Add the incident to the result object
//				if (results != null)
//					results.addException("Memory threshold reached");
//
//				// We stop the data flow analysis
//				for (IMemoryBoundedSolver solver : solvers)
//					solver.forceTerminate();
//				logger.warn("Running out of memory, solvers terminated");
//			}
//
//		});
		MemoryWarningSystem.setWarningThreshold(0.999d);
		this.results = res;
	}
	
	/**
	 * Adds a solver that shall be terminated when the memory threshold is reached
	 * @param solver A solver that shall be terminated when the memory threshold
	 * is reached
	 */
	public void addSolver(IMemoryBoundedSolver solver) {
		this.solvers.add(solver);
	}
	
	/**
	 * Removes the given solver from the watch list. The given solver will no
	 * longer ne notified when the memory threshold is reached.
	 * @param solver The solver to remove from the watch list
	 * @return True if the given solver was found in the watch list, otherwise
	 * false
	 */
	public boolean removeSolver(IMemoryBoundedSolver solver) {
		return this.solvers.remove(solver);
	}
	
	/**
	 * Clears the list of solvers registered with this memory watcher
	 */
	public void clearSolvers() {
		this.solvers.clear();
	}
	
	/**
	 * Shuts down the memory watcher and frees all resources associated with it
	 */
	public void close() {
		clearSolvers();
		warningSystem.close();
	}

}
