/*******************************************************************************
 * Copyright (c) 2012 Secure Software Engineering Group at EC SPRIDE.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Lesser Public License v2.1
 * which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
 * 
 * Contributors: Christian Fritz, Steven Arzt, Siegfried Rasthofer, Eric
 * Bodden, and others.
 ******************************************************************************/
package soot.jimple.infoflow.sparseOptimization.solver;

import heros.FlowFunction;
import heros.solver.Pair;
import heros.solver.PathEdge;
import soot.*;
import soot.jimple.*;
import soot.jimple.infoflow.aliasing.Aliasing;
import soot.jimple.infoflow.collect.MyConcurrentHashMap;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.problems.AbstractInfoflowProblem;
import soot.jimple.infoflow.solver.IFollowReturnsPastSeedsHandler;
import soot.jimple.infoflow.solver.IInfoflowSolver;
import soot.jimple.infoflow.solver.executors.InterruptableExecutor;
import soot.jimple.infoflow.solver.fastSolver.IFDSSolver;
import soot.jimple.infoflow.solver.functions.SolverCallFlowFunction;
import soot.jimple.infoflow.solver.functions.SolverCallToReturnFlowFunction;
import soot.jimple.infoflow.solver.functions.SolverNormalFlowFunction;
import soot.jimple.infoflow.solver.functions.SolverReturnFlowFunction;
import soot.jimple.infoflow.sparseOptimization.problem.SparseInfoflowProblem;
import soot.jimple.toolkits.ide.icfg.BiDiInterproceduralCFG;

import java.util.*;

/**
 * We are subclassing the JimpleIFDSSolver because we need the same executor for both the forward and the backward analysis
 * Also we need to be able to insert edges containing new taint information
 * 
 */
public class InfoflowSparseSolver extends IFDSSolver<Unit, Abstraction, BiDiInterproceduralCFG<Unit, SootMethod>>
		implements IInfoflowSolver {

	private IFollowReturnsPastSeedsHandler followReturnsPastSeedsHandler = null;
	private final AbstractInfoflowProblem problem;


	public static long sptime = 0;

	public InfoflowSparseSolver(AbstractInfoflowProblem problem, InterruptableExecutor executor) {
		super(problem);
		this.problem = problem;
		this.executor = executor;
		problem.setSolver(this);		
	}
	
	@Override
	protected InterruptableExecutor getExecutor() {
		return executor;
	}

	@Override
	public boolean processEdge(PathEdge<Unit, Abstraction> edge, Unit defStmt, Set<Integer> bbSet){
		propagate(bbSet, defStmt, edge.factAtSource(), edge.getTarget(), edge.factAtTarget(), null, false, true);
		return true;
	}

	@Override
	public boolean processEdge(PathEdge<Unit, Abstraction> edge){
		//propagate(defStmt, edge.factAtSource(), edge.getTarget(), edge.factAtTarget(), null, false, true);
		return false;
	}

	protected PathEdge<Unit, Abstraction> activateEdge(PathEdge<Unit, Abstraction> oldEdge, Unit defStmt, Set<Integer> bbSet) {
		Abstraction source = oldEdge.factAtTarget();
		Unit src = oldEdge.getTarget();
		if (!source.isAbstractionActive()){
			SootMethod m = problem.getManager().getICFG().getMethodOf(src);
			Unit activeStmt = source.getActivationUnit();
			//BasicBlockGraph orderComputing = DataFlowGraphQuery.v().getMethodToBasicBlockGraphMap().get(m);
			Unit targetCallStmt = problem.getManager().getICFG().isCallStmt(src)? src: null;
			//Unit targetCallStmt =  null;
			boolean isStartPoint = problem.getManager().getICFG().isStartPoint(src);
			Unit activeStmtInMethod = problem.isActivatingTaint(m,
					activeStmt, defStmt, src, targetCallStmt);
			if((bbSet == null && !isStartPoint && activeStmtInMethod != null)
					) {

				long beforesp = System.nanoTime();
				//boolean isSp =  false;
				boolean isSp =  isStrongUpdate(source.clone(), defStmt, activeStmtInMethod, src);
				sptime += (System.nanoTime() - beforesp);
				if(!isSp) {
					Abstraction newSource = source.getActiveCopy();
					PathEdge<Unit, Abstraction> activeEdge = new PathEdge<>(oldEdge.factAtSource(), oldEdge.getTarget(), newSource);
					return activeEdge;
				}

			} else if((bbSet != null && !isStartPoint &&
					problem.isActivatingTaintUsingbbSet(m, activeStmt,
							defStmt, src, targetCallStmt, bbSet))) {
				Abstraction newSource = source.getActiveCopy();
				PathEdge<Unit, Abstraction> activeEdge = new PathEdge<>(oldEdge.factAtSource(), oldEdge.getTarget(), newSource);
				return activeEdge;
			}

		}
			return oldEdge;
	}

	boolean isStrongUpdate(Abstraction source, Unit src , Unit activeStmtInMethod, Unit dest) {

		if(activeStmtInMethod.equals(dest))
			return false;
		Queue<Pair<Unit, Abstraction>> worklist = new LinkedList<>();
		Pair<Unit, Abstraction> sourceKey = new Pair<Unit, Abstraction>(src, source);
		worklist.offer(sourceKey);
		Set<Pair<Unit, Abstraction>> visited = new HashSet<>();
		visited.add(sourceKey);
		boolean isroot = true;
		while(!worklist.isEmpty()) {
			Pair<Unit, Abstraction> curPath = worklist.poll();

			Unit curUnit = curPath.getO1();
			Abstraction curAbs = curPath.getO2();

			if(isroot) {
				isroot = false;
			}else {
				boolean isNewActiveTaint = false;
				if(curUnit.equals(activeStmtInMethod) && !curAbs.isAbstractionActive()) {
					curAbs = curAbs.getActiveCopy();
					isNewActiveTaint = true;
				}

				if(curUnit.equals(dest)){
					if(curAbs.isAbstractionActive()) {
						return false;
					}else {
						continue;
					}
				}

				if(subIsSp(curAbs, curUnit) && !isNewActiveTaint) {
					continue;
				}
			}

			for(Unit next : problem.getManager().getICFG().getSuccsOf(curUnit)) {

				Pair<Unit, Abstraction> nextKey = new Pair<Unit, Abstraction>(next, curAbs);
				if(visited.contains(nextKey)) {
					continue;
				}
				visited.add(nextKey);
				worklist.offer(nextKey);
			}
		}
		return true;
	}


	private boolean subIsSp(Abstraction source, Unit src) {

		if(problem.getManager().getICFG().isCallStmt(src)) {
			return spCallFlow(source, (Stmt) src);
		}else {
			return spNormalFlow(source, src);
		}
		//return false;
	}

	public boolean spCallFlow(Abstraction source, Stmt stmt) {
		if(stmt instanceof AssignStmt) {
			final AssignStmt assignStmt = (AssignStmt) stmt;
			final Value left = assignStmt.getLeftOp();
			if(Aliasing.baseMatches(left, source))
				return true;
		}
		final InvokeExpr ie = (stmt != null && stmt.containsInvokeExpr())
				? stmt.getInvokeExpr() : null;
		if(ie != null) {

			if(ie instanceof InstanceInvokeExpr) {
				// add invoke stmt's base, such as  a.foo()
				InstanceInvokeExpr vie = (InstanceInvokeExpr) ie;
				if(Aliasing.myBaseMatches(vie.getBase(), source))
					return true;
			}

			for (int i = 0; i < ie.getArgCount(); i++) {
				if(Aliasing.myBaseMatches(ie.getArg(i), source))
					return true;
			}
		}


		return false;
	}

	public boolean spNormalFlow(Abstraction source, Unit stmt) {
		if (!(stmt instanceof AssignStmt))
			return false;
		AssignStmt assignStmt = (AssignStmt) stmt;

		//if leftvalue contains the tainted value -> it is overwritten - remove taint:
		//but not for arrayRefs:
		// x[i] = y --> taint is preserved since we do not distinguish between elements of collections
		//because we do not use a MUST-Alias analysis, we cannot delete aliases of taints
		if (assignStmt.getLeftOp() instanceof ArrayRef)
			return false;

		// If this is a newly created alias at this statement, we don't kill it right away
		if (!source.isAbstractionActive() && source.getCurrentStmt() == stmt)
			return false;

		// If the statement has just been activated, we do not overwrite stuff
		if (source.getPredecessor() != null
				&& !source.getPredecessor().isAbstractionActive()
				&& source.isAbstractionActive()
				&& source.getPredecessor().getActivationUnit() == stmt
				&& source.getAccessPath().equals(source.getPredecessor().getAccessPath()))
			return false;

		if (source.getAccessPath().isInstanceFieldRef()) {
			// Data Propagation: x.f = y && x.f tainted --> no taint propagated
			// Alias Propagation: Only kill the alias if we directly overwrite it,
			// otherwise it might just be the creation of yet another alias
			if (assignStmt.getLeftOp() instanceof InstanceFieldRef) {
				InstanceFieldRef leftRef = (InstanceFieldRef) assignStmt.getLeftOp();
				boolean baseAliases;
				if (source.isAbstractionActive())
					baseAliases =   ((SparseInfoflowProblem)problem).getAliasing().mustAlias((Local) leftRef.getBase(),
							source.getAccessPath().getPlainValue(), assignStmt);
				else
					baseAliases = leftRef.getBase() == source.getAccessPath().getPlainValue();
				if (baseAliases) {
					if (((SparseInfoflowProblem)problem).getAliasing().mustAlias(leftRef.getField(), source.getAccessPath().getFirstField())) {
						return true;
//						killAll.value = true;
//						return null;
					}
				}
			}
			// x = y && x.f tainted -> no taint propagated. This must only check the precise
			// variable which gets replaced, but not any potential strong aliases
			else if (assignStmt.getLeftOp() instanceof Local){
				if (((SparseInfoflowProblem)problem).getAliasing().mustAlias((Local) assignStmt.getLeftOp(),
						source.getAccessPath().getPlainValue(), (Stmt) stmt)) {
					return true;
//					killAll.value = true;
//					return null;
				}
			}
		}
		//X.f = y && X.f tainted -> no taint propagated. Kills are allowed even if
		// static field tracking is disabled
		else if (source.getAccessPath().isStaticFieldRef()){
			if (assignStmt.getLeftOp() instanceof StaticFieldRef
					&& ((SparseInfoflowProblem)problem).getAliasing().mustAlias(((StaticFieldRef) assignStmt.getLeftOp()).getField(),
					source.getAccessPath().getFirstField())) {
				return true;
//				killAll.value = true;
//				return null;
			}

		}
		//when the fields of an object are tainted, but the base object is overwritten
		// then the fields should not be tainted any more
		//x = y && x.f tainted -> no taint propagated
		else if (source.getAccessPath().isLocal()
				&& assignStmt.getLeftOp() instanceof Local
				&& assignStmt.getLeftOp() == source.getAccessPath().getPlainValue()) {
			// If there is also a reference to the tainted value on the right side, we
			// must only kill the source, but give the other rules the possibility to
			// re-create the taint
			boolean found = false;
			for (ValueBox vb : assignStmt.getRightOp().getUseBoxes())
				if (vb.getValue() == source.getAccessPath().getPlainValue()) {
					found = true;
					break;
				}

//			killAll.value = !found;
//			killSource.value = true;
			return true;
			//return null;
		}

		return false;
		//return null;
	}




	
	@Override
	public void injectContext(IInfoflowSolver otherSolver, SootMethod callee,
			Abstraction d3, Unit callSite, Abstraction d2, Abstraction d1) {
		if (!addIncoming(callee, d3, callSite, d1, d2))
			return;
		
		Set<Pair<Unit, Abstraction>> endSumm = endSummary(callee, d3);		
		if (endSumm != null) {
			Collection<Unit> returnSiteNs = icfg.getReturnSitesOfCallAt(callSite);
			for(Pair<Unit, Abstraction> entry: endSumm) {
				Unit eP = entry.getO1();
				Abstraction d4 = entry.getO2();
				//for each return site
				for(Unit retSiteN: returnSiteNs) {
					//compute return-flow function
					FlowFunction<Abstraction> retFunction = flowFunctions.getReturnFlowFunction(callSite, callee, eP, retSiteN);
					//for each target value of the function
					for(Abstraction d5: computeReturnFlowFunction(retFunction, d3, d4, callSite, Collections.singleton(d1))) {
						if (memoryManager != null)
							d5 = memoryManager.handleGeneratedMemoryObject(d4, d5);
						
						// If we have not changed anything in the callee, we do not need the facts
						// from there. Even if we change something: If we don't need the concrete
						// path, we can skip the callee in the predecessor chain
						Abstraction d5p = d5;
						if (d5.equals(d2)) {
							d5p = d2;
							d5p.setUseStmts(d5.getUseStmts());
						}
						else if (setJumpPredecessors && d5p != d2) {
							d5p = d5p.clone();
							d5p.setPredecessor(d2);
						}
						if(d5p.getUseStmts() == null)
							throw new RuntimeException("return abs should have a use stmt set");
						//propagateWapper(retSiteC, d4, retSiteC, d5p, c, false, true);
						// fix bug, inject context
						propagateWapper(callSite, d1, retSiteN, d5p, callSite, false, true);
					}
				}
			}
		}
	}
	
	@Override
	protected Set<Abstraction> computeReturnFlowFunction(
			FlowFunction<Abstraction> retFunction,
			Abstraction d1,
			Abstraction d2,
			Unit callSite,
			Collection<Abstraction> callerSideDs) {
		if (retFunction instanceof SolverReturnFlowFunction) {
			// Get the d1s at the start points of the caller
			return ((SolverReturnFlowFunction) retFunction).computeTargets(d2, d1, callerSideDs);
		}
		else
			return retFunction.computeTargets(d2);
	}

	@Override
	protected Set<Abstraction> computeNormalFlowFunction
			(FlowFunction<Abstraction> flowFunction, Abstraction d1, Abstraction d2) {
		if (flowFunction instanceof SolverNormalFlowFunction)
			return ((SolverNormalFlowFunction) flowFunction).computeTargets(d1, d2);
		else
			return flowFunction.computeTargets(d2);
	}

	@Override
	protected Set<Abstraction> computeCallToReturnFlowFunction
			(FlowFunction<Abstraction> flowFunction, Abstraction d1, Abstraction d2) {
		if (flowFunction instanceof SolverCallToReturnFlowFunction)
			return ((SolverCallToReturnFlowFunction) flowFunction).computeTargets(d1, d2);
		else
			return flowFunction.computeTargets(d2);		
	}

	@Override
	protected Set<Abstraction> computeCallFlowFunction
			(FlowFunction<Abstraction> flowFunction, Abstraction d1, Abstraction d2) {
		if (flowFunction instanceof SolverCallFlowFunction)
			return ((SolverCallFlowFunction) flowFunction).computeTargets(d1, d2);
		else
			return flowFunction.computeTargets(d2);		
	}
	
	@Override
	public void cleanup() {
		this.jumpFunctions = new MyConcurrentHashMap<PathEdge<Unit, Abstraction>, Abstraction>();
		this.incoming.clear();
		this.endSummary.clear();
	}
	
	@Override
	public Set<Pair<Unit, Abstraction>> endSummary(SootMethod m, Abstraction d3) {
		return super.endSummary(m, d3);
	}
	
	@Override
	protected void processExit(PathEdge<Unit, Abstraction> edge) {
		super.processExit(edge);
		
		if (followReturnsPastSeeds && followReturnsPastSeedsHandler != null) {
			final Abstraction d1 = edge.factAtSource();
			final Unit u = edge.getTarget();
			final Abstraction d2 = edge.factAtTarget();
			
			final SootMethod methodThatNeedsSummary = icfg.getMethodOf(u);
			final Map<Unit, Map<Abstraction, Abstraction>> inc = incoming(d1, methodThatNeedsSummary);
			
			if (inc == null || inc.isEmpty())
				followReturnsPastSeedsHandler.handleFollowReturnsPastSeeds(d1, u, d2);
		}
	}
	
	@Override
	public void setFollowReturnsPastSeedsHandler(IFollowReturnsPastSeedsHandler handler) {
		this.followReturnsPastSeedsHandler = handler;
	}

	@Override
	public long getPropagationCount() {
		return propagationCount;
	}

	@Override
	public AbstractInfoflowProblem getTabulationProblem() {
		return problem;
	}
	
}
