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
package soot.jimple.infoflow.sparseOptimization.problem;

import heros.FlowFunction;
import heros.FlowFunctions;
import heros.flowfunc.Identity;
import heros.flowfunc.KillAll;
import heros.solver.PathEdge;
import soot.*;
import soot.jimple.*;
import soot.jimple.infoflow.InfoflowManager;
import soot.jimple.infoflow.aliasing.Aliasing;
import soot.jimple.infoflow.collect.MutableTwoElementSet;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.handlers.TaintPropagationHandler.FlowFunctionType;
import soot.jimple.infoflow.problems.AbstractInfoflowProblem;
import soot.jimple.infoflow.solver.functions.SolverCallFlowFunction;
import soot.jimple.infoflow.solver.functions.SolverCallToReturnFlowFunction;
import soot.jimple.infoflow.solver.functions.SolverNormalFlowFunction;
import soot.jimple.infoflow.solver.functions.SolverReturnFlowFunction;
import soot.jimple.infoflow.sparseOptimization.dataflowgraph.DataFlowGraphQuery;
import soot.jimple.infoflow.sparseOptimization.dataflowgraph.data.DataFlowNode;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;
import soot.jimple.infoflow.util.BaseSelector;
import soot.jimple.infoflow.util.TypeUtils;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * class which contains the flow functions for the backwards solver. This is
 * required for on-demand alias analysis.
 */
public class BackwardsSparseInfoflowProblem extends AbstractInfoflowProblem {

	public void setTaintWrapper(ITaintPropagationWrapper wrapper) {
		taintWrapper = wrapper;
	}

	public BackwardsSparseInfoflowProblem(InfoflowManager manager) {
		super(manager);
	}
	
	@Override
	public FlowFunctions<Unit, Abstraction, SootMethod> createFlowFunctionsFactory() {
		return new FlowFunctions<Unit, Abstraction, SootMethod>() {
			
			private Abstraction checkAbstraction(Abstraction abs) {
				if (abs == null)
					return null;
				
				// Primitive types and strings cannot have aliases and thus
				// never need to be propagated back
				if (!abs.getAccessPath().isStaticFieldRef()) {
					if (abs.getAccessPath().getBaseType() instanceof PrimType)
						return null;
					if (TypeUtils.isStringType(abs.getAccessPath().getBaseType())
							&& !abs.getAccessPath().getCanHaveImmutableAliases())
						return null;
				}
				else {
					if (abs.getAccessPath().getFirstFieldType() instanceof PrimType)
						return null;
					if (TypeUtils.isStringType(abs.getAccessPath().getFirstFieldType())
							&& !abs.getAccessPath().getCanHaveImmutableAliases())
						return null;
				}
				return abs;
			}

			/**
			 * Computes the aliases for the given statement
			 * @param defStmt The definition statement from which to extract
			 * the alias information
			 * @param leftValue The left side of def. Passed in to allow for
			 * caching, no need to recompute this for every abstraction being
			 * processed.
			 * @param d1 The abstraction at the method's start node
			 * @param source The source abstraction of the alias search
			 * from before the current statement
			 * @return The set of abstractions after the current statement
			 */
			private Set<Abstraction> computeAliases
					(final DefinitionStmt defStmt,
					Value leftValue,
					Abstraction d1,
					Abstraction source) {
				assert !source.getAccessPath().isEmpty();
				
				// A backward analysis looks for aliases of existing taints and thus
				// cannot create new taints out of thin air
				if (source == getZeroValue())
					return Collections.emptySet();
				
				final Set<Abstraction> res = new MutableTwoElementSet<Abstraction>();
				
				// Check whether the left side of the assignment matches our
				// current taint abstraction
				final boolean leftSideMatches = Aliasing.baseMatches(leftValue, source);
				if (!leftSideMatches){
					//res.add(source);
				}
				else {
					// The left side is overwritten completely
					
					// If we have an assignment to the base local of the current taint,
					// all taint propagations must be below that point, so this is the
					// right point to turn around.


					// a.f1 = b ;  or  a = b ; or a.f2 = b; a = new ;
					//
					// a.f1 = pwd;

					Set<Unit> nextSet = getNextStmtFromForwardDfg(leftValue, defStmt, source);
					for (Unit u : nextSet)
						manager.getForwardSolver().processEdge(new PathEdge<Unit, Abstraction>(d1, u, source));

//					for (Unit u : interproceduralCFG().getPredsOf(defStmt))
//						manager.getForwardSolver().processEdge(new PathEdge<Unit, Abstraction>(d1, u, source));
				}
				
				// We only handle assignments and identity statements
				if (defStmt instanceof IdentityStmt) {
					//res.add(source);
					return res;
				}
				if (!(defStmt instanceof AssignStmt))
					return res;
				
				// Get the right side of the assignment
				final Value rightValue = BaseSelector.selectBase(defStmt.getRightOp(), false);
				
				// Is the left side overwritten completely?
				if (leftSideMatches) {
					// Termination shortcut: If the right side is a value we do not track,
					// we can stop here.
					if (!(rightValue instanceof Local || rightValue instanceof FieldRef))
						return Collections.emptySet();
				}
				
				// If we assign a constant, there is no need to track the right side
				// any further or do any forward propagation since constants cannot
				// carry taint.
				if (rightValue instanceof Constant)
					return res;
				
				// If this statement creates a new array, we cannot track upwards the size
				if (defStmt.getRightOp() instanceof NewArrayExpr)
					return res;
				
				// We only process heap objects. Binary operations can only
				// be performed on primitive objects.
				if (defStmt.getRightOp() instanceof BinopExpr)
					return res;
				if (defStmt.getRightOp() instanceof UnopExpr)
					return res;
				
				// If we have a = x with the taint "x" being inactive,
				// we must not taint the left side. We can only taint
				// the left side if the tainted value is some "x.y".
				boolean aliasOverwritten = Aliasing.baseMatchesStrict(rightValue, source)
						&& rightValue.getType() instanceof RefType
						&& !source.dependsOnCutAP();
				
				if (!aliasOverwritten && !(rightValue.getType() instanceof PrimType)) {
					// If the tainted value 'b' is assigned to variable 'a' and 'b'
					// is a heap object, we must also look for aliases of 'a' upwards
					// from the current statement.
					Abstraction newLeftAbs = null;
					if (rightValue instanceof InstanceFieldRef) {
						InstanceFieldRef ref = (InstanceFieldRef) rightValue;
						if (source.getAccessPath().isInstanceFieldRef()
								&& ref.getBase() == source.getAccessPath().getPlainValue()
								&& source.getAccessPath().firstFieldMatches(ref.getField())) {
							AccessPath ap = manager.getAccessPathFactory().copyWithNewValue(
									source.getAccessPath(), leftValue, source.getAccessPath().getFirstFieldType(), true);
							newLeftAbs = checkAbstraction(source.deriveNewAbstraction(ap, defStmt));
						}
					}
					else if (manager.getConfig().getEnableStaticFieldTracking()
							&& rightValue instanceof StaticFieldRef) {
						StaticFieldRef ref = (StaticFieldRef) rightValue;
						if (source.getAccessPath().isStaticFieldRef()
								&& source.getAccessPath().firstFieldMatches(ref.getField())) {
							AccessPath ap = manager.getAccessPathFactory().copyWithNewValue(source.getAccessPath(),
									leftValue, source.getAccessPath().getBaseType(), true);
							newLeftAbs = checkAbstraction(source.deriveNewAbstraction(ap, defStmt));
						}
					}
					else if (rightValue == source.getAccessPath().getPlainValue()) {
						Type newType = source.getAccessPath().getBaseType();
						if (leftValue instanceof ArrayRef)
							newType = TypeUtils.buildArrayOrAddDimension(newType);
						else if (defStmt.getRightOp() instanceof ArrayRef)
							newType = ((ArrayType) newType).getElementType();
						
						// Type check
						if (!manager.getTypeUtils().checkCast(source.getAccessPath(),
								defStmt.getRightOp().getType()))
							return Collections.emptySet();
						
						// If the cast was realizable, we can assume that we had the
						// type to which we cast. Do not loosen types, though.
						if (defStmt.getRightOp() instanceof CastExpr) {
							CastExpr ce = (CastExpr) defStmt.getRightOp();								
							if (!manager.getHierarchy().canStoreType(newType, ce.getCastType()))
								newType = ce.getCastType();
						}
						// Special type handling for certain operations
						else if (defStmt.getRightOp() instanceof LengthExpr) {
							// ignore. The length of an array is a primitive and thus
							// cannot have aliases
							return res;
						}
						else if (defStmt.getRightOp() instanceof InstanceOfExpr) {
							// ignore. The type check of an array returns a
							// boolean which is a primitive and thus cannot
							// have aliases
							return res;
						}
						
						if (newLeftAbs == null) {
							AccessPath ap = manager.getAccessPathFactory().copyWithNewValue(source.getAccessPath(),
									leftValue, newType, false);
							newLeftAbs = checkAbstraction(source.deriveNewAbstraction(ap, defStmt));
						}
					}
					
					if (newLeftAbs != null) {
						// If we ran into a new abstraction that points to a
						// primitive value, we can remove it
						if (newLeftAbs.getAccessPath().getLastFieldType() instanceof PrimType)
							return res;
						
						if (!newLeftAbs.getAccessPath().equals(source.getAccessPath())) {

							res.add(getAbsFromBackwardDfg(leftValue, defStmt, newLeftAbs));
							// Propagate the new alias upwards
							//res.add(newLeftAbs);

							Set<Unit> nextSet = getNextStmtFromForwardDfg(leftValue, defStmt, newLeftAbs);
							for (Unit u : nextSet)
								manager.getForwardSolver().processEdge(new PathEdge<Unit, Abstraction>(d1, u, newLeftAbs));


//							// Propagate the new alias upwards
//							res.add(newLeftAbs);
//
//							// Inject the new alias into the forward solver
//							for (Unit u : interproceduralCFG().getPredsOf(defStmt))
//								manager.getForwardSolver().processEdge(new PathEdge<Unit, Abstraction>(d1, u, newLeftAbs));
						}
					}
				}
				
				// If we have the tainted value on the left side of the assignment,
				// we also have to look or aliases of the value on the right side of
				// the assignment.
				if ((rightValue instanceof Local || rightValue instanceof FieldRef)
						&& !(leftValue.getType() instanceof PrimType)) {
					boolean addRightValue = false;
					boolean cutFirstField = false;
					Type targetType = null;
					
					// if both are fields, we have to compare their fieldName via equals and their bases via PTS
					if (leftValue instanceof InstanceFieldRef) {
						if (source.getAccessPath().isInstanceFieldRef()) {
							InstanceFieldRef leftRef = (InstanceFieldRef) leftValue;
							if (leftRef.getBase() == source.getAccessPath().getPlainValue()) {
								if (source.getAccessPath().firstFieldMatches(leftRef.getField())) {
									targetType = source.getAccessPath().getFirstFieldType();
									addRightValue = true;
									cutFirstField = true;
								}
							}
						}
						// indirect taint propagation:
						// if leftValue is local and source is instancefield of this local:
					} else if (leftValue instanceof Local && source.getAccessPath().isInstanceFieldRef()) {
						Local base = source.getAccessPath().getPlainValue();
						if (leftValue == base) {
							targetType = source.getAccessPath().getBaseType();
							addRightValue = true;
						}
					} else if (leftValue instanceof ArrayRef) {
						ArrayRef ar = (ArrayRef) leftValue;
						Local leftBase = (Local) ar.getBase();
						if (leftBase == source.getAccessPath().getPlainValue()) {
							addRightValue = true;
							targetType = source.getAccessPath().getBaseType();
						}
						// generic case, is true for Locals, ArrayRefs that are equal etc..
					} else if (leftValue == source.getAccessPath().getPlainValue()) {
						// If this is an unrealizable cast, we can stop propagating
						if (!manager.getTypeUtils().checkCast(source.getAccessPath(), leftValue.getType()))
							return Collections.emptySet();
						
						addRightValue = true;
						targetType = source.getAccessPath().getBaseType();
					}
					
					// if one of them is true -> add rightValue
					if (addRightValue) {
						if (targetType != null) {
							// Special handling for some operations
							if (defStmt.getRightOp() instanceof ArrayRef)
								targetType = TypeUtils.buildArrayOrAddDimension(targetType);
							else if (leftValue instanceof ArrayRef) {
								assert source.getAccessPath().getBaseType() instanceof ArrayType;
								targetType = ((ArrayType) targetType).getElementType();
								
								// If we have a type of java.lang.Object, we try to tighten it
								if (TypeUtils.isObjectLikeType(targetType))
									targetType = rightValue.getType();
								
								// If the types do not match, the right side cannot be an alias
								if (!manager.getTypeUtils().checkCast(rightValue.getType(), targetType))
									addRightValue = false;
							}
						}
						
						// Special type handling for certain operations
						if (defStmt.getRightOp() instanceof LengthExpr)
							targetType = null;
						
						// We do not need to handle casts. Casts only make
						// types more imprecise when going backwards.

						// If the source has fields, we may not have a primitive type
						if (targetType instanceof PrimType || (targetType instanceof ArrayType
								&& ((ArrayType) targetType).getElementType() instanceof PrimType))
							if (!source.getAccessPath().isStaticFieldRef() && !source.getAccessPath().isLocal())
								return Collections.emptySet();
						if (rightValue.getType() instanceof PrimType || (rightValue.getType() instanceof ArrayType
								&& ((ArrayType) rightValue.getType()).getElementType() instanceof PrimType))
							if (!source.getAccessPath().isStaticFieldRef() && !source.getAccessPath().isLocal())
								return Collections.emptySet();
						
						// If the right side's type is not compatible with our current type,
						// this cannot be an alias
						if (addRightValue) {
							if (!manager.getTypeUtils().checkCast(rightValue.getType(), targetType))
								addRightValue = false;
						}
						
						// Make sure to only track static fields if it has been enabled
						if (addRightValue)
							if (!manager.getConfig().getEnableStaticFieldTracking()
									&& rightValue instanceof StaticFieldRef)
								addRightValue = false;

						if (addRightValue) {
							AccessPath ap = manager.getAccessPathFactory().copyWithNewValue(source.getAccessPath(),
									rightValue, targetType, cutFirstField);
							Abstraction newAbs = checkAbstraction(source.deriveNewAbstraction(ap, defStmt));
							if (newAbs != null && !newAbs.getAccessPath().equals(source.getAccessPath())) {
								res.add(getAbsFromBackwardDfg(rightValue, defStmt, newAbs));
								//res.add(newAbs);

								Set<Unit> nextSet = getNextStmtFromForwardDfg(rightValue, defStmt, newAbs);
								for (Unit u : nextSet)
									manager.getForwardSolver().processEdge(new PathEdge<Unit, Abstraction>(d1, u, newAbs));

								// Inject the new alias into the forward solver
//								for (Unit u : interproceduralCFG().getPredsOf(defStmt))
//									manager.getForwardSolver().processEdge(new PathEdge<Unit, Abstraction>(d1, u, newAbs));
							}
						}
					}
				}
				
				return res;
			}

			private Abstraction getAbsFromBackwardDfg(Value value , Unit stmt, Abstraction abs) {
				DataFlowNode dataFlowNode = DataFlowGraphQuery.v().useValueTofindBackwardDataFlowGraph(value, stmt);

				return dataFlowNode.deriveNewAbsbyAbs(abs);
			}

			private Set<Unit> getNextStmtFromForwardDfg(Value value , Unit stmt, Abstraction abs) {
				Set<Unit> res = new HashSet<>();
				DataFlowNode dataFlowNode = DataFlowGraphQuery.v().useValueTofindForwardDataFlowGraph(value, stmt);
				AccessPath ap = abs.getAccessPath();
				SootField firstField = ap.getFirstField();
				if(dataFlowNode !=null &&  dataFlowNode.getSuccs() != null) {
					Set<DataFlowNode> next = dataFlowNode.getSuccs().get(DataFlowNode.baseField);
					if(next != null)
						for(DataFlowNode d : next) {
							res.add(d.getStmt());
						}

					if(firstField != null) {
						Set<DataFlowNode> next1 = dataFlowNode.getSuccs().get(firstField);
						if(next1 != null)
							for(DataFlowNode d : next1) {
								res.add(d.getStmt());
							}
					}
				}
				return res;
			}


			
			@Override
			public FlowFunction<Abstraction> getNormalFlowFunction(final Unit src, final Unit dest) {
				

				if (src instanceof DefinitionStmt) {
					final DefinitionStmt defStmt = (DefinitionStmt) src;
					final Value leftValue = BaseSelector.selectBase(defStmt.getLeftOp(), true);
					
					final DefinitionStmt destDefStmt = dest instanceof DefinitionStmt
							? (DefinitionStmt) dest : null;
					final Value destLeftValue = destDefStmt == null ? null : BaseSelector.selectBase
							(destDefStmt.getLeftOp(), true);

					return new SolverNormalFlowFunction() {

						@Override
						public Set<Abstraction> computeTargets(Abstraction d1, Abstraction source) {
							if (source == getZeroValue())
								return Collections.emptySet();
							assert source.isAbstractionActive() || manager.getConfig().getFlowSensitiveAliasing();
							
							// Notify the handler if we have one
							if (taintPropagationHandler != null)
								taintPropagationHandler.notifyFlowIn(src, source, interproceduralCFG(),
										FlowFunctionType.NormalFlowFunction);
							
							Set<Abstraction> res = computeAliases(defStmt, leftValue, d1, source);
							
							if (destDefStmt != null && interproceduralCFG().isExitStmt(destDefStmt))
								for (Abstraction abs : res)
									computeAliases(destDefStmt, destLeftValue, d1, abs);
							
							return notifyOutFlowHandlers(src, d1, source, res,
									FlowFunctionType.NormalFlowFunction);
						}

					};
				}
				return Identity.v();
			}

			@Override
			public FlowFunction<Abstraction> getCallFlowFunction(final Unit src, final SootMethod dest) {
				if (!dest.isConcrete())
					return KillAll.v();
								
				final Stmt stmt = (Stmt) src;
				final InvokeExpr ie = (stmt != null && stmt.containsInvokeExpr())
						? stmt.getInvokeExpr() : null;
				final boolean isReflectiveCallSite = interproceduralCFG().isReflectiveCallSite(ie);

				final Value[] paramLocals = new Value[dest.getParameterCount()]; 
				for (int i = 0; i < dest.getParameterCount(); i++)
					paramLocals[i] = dest.getActiveBody().getParameterLocal(i);
				
				final boolean isSource = manager.getSourceSinkManager() != null
						? manager.getSourceSinkManager().getSourceInfo((Stmt) src, manager) != null : false;
				final boolean isSink = manager.getSourceSinkManager() != null
						? manager.getSourceSinkManager().isSink(stmt, manager, null) : false;
				
				// This is not cached by Soot, so accesses are more expensive
				// than one might think
				final Local thisLocal = dest.isStatic() ? null : dest.getActiveBody().getThisLocal();	
				
				// Android executor methods are handled specially. getSubSignature()
				// is slow, so we try to avoid it whenever we can
				final boolean isExecutorExecute = interproceduralCFG().isExecutorExecute(ie, dest);
				
				return new SolverCallFlowFunction() {

					@Override
					public Set<Abstraction> computeTargets(Abstraction d1, Abstraction source) {
						if (source == getZeroValue())
							return Collections.emptySet();
						assert source.isAbstractionActive() || manager.getConfig().getFlowSensitiveAliasing();
						
						// Notify the handler if we have one
						if (taintPropagationHandler != null)
							taintPropagationHandler.notifyFlowIn(stmt, source, interproceduralCFG(),
									FlowFunctionType.CallFlowFunction);
						
						//if we do not have to look into sources or sinks:
						if (!manager.getConfig().getInspectSources() && isSource)
							return Collections.emptySet();
						if (!manager.getConfig().getInspectSinks() && isSink)
							return Collections.emptySet();
						
						// Do not propagate in inactive taints that will be
						// activated there since they already came out of the
						// callee
						if (isCallSiteActivatingTaint(stmt, source.getActivationUnit()))
							return Collections.emptySet();
						
						// Do not analyze static initializers if static field
						// tracking is disabled
						if (!manager.getConfig().getEnableStaticFieldTracking() && dest.isStaticInitializer())
							return Collections.emptySet();
						
						// taint is propagated in CallToReturnFunction, so we do not
						// need any taint here if the taint wrapper is exclusive:
						if(taintWrapper != null && taintWrapper.isExclusive(stmt, source))
							return Collections.emptySet();
						
						// Do not propagate into Soot library classes if that
						// optimization is enabled
						if (isExcluded(dest))
							return Collections.emptySet();
						
						// Only propagate the taint if the target field is actually read
						if (manager.getConfig().getEnableStaticFieldTracking()
								&& source.getAccessPath().isStaticFieldRef())
							if (!interproceduralCFG().isStaticFieldRead(dest,
									source.getAccessPath().getFirstField()))
								return Collections.emptySet();
						
						Set<Abstraction> res = new HashSet<Abstraction>();
						
						// if the returned value is tainted - taint values from return statements
						if (src instanceof DefinitionStmt) {
							DefinitionStmt defnStmt = (DefinitionStmt) src;
							Value leftOp = defnStmt.getLeftOp();
							if (leftOp == source.getAccessPath().getPlainValue()) {
								// look for returnStmts:
								for (Unit u : dest.getActiveBody().getUnits()) {
									if (u instanceof ReturnStmt) {
										ReturnStmt rStmt = (ReturnStmt) u;
										if (rStmt.getOp() instanceof Local
												|| rStmt.getOp() instanceof FieldRef)
											if (manager.getTypeUtils().checkCast(source.getAccessPath(), rStmt.getOp().getType())) {
												AccessPath ap = manager.getAccessPathFactory().copyWithNewValue
														(source.getAccessPath(), rStmt.getOp(), null, false);
												Abstraction abs = checkAbstraction(source.deriveNewAbstraction(ap, (Stmt) src));
												if (abs != null) {
													 res.add(useValueTofindCallInfo(rStmt.getOp(), rStmt, abs));
												}
													//res.add(abs);
											}
									}
								}
							}
						}

						// easy: static
						if (manager.getConfig().getEnableStaticFieldTracking()
								&& source.getAccessPath().isStaticFieldRef()) {
							Abstraction abs = checkAbstraction(source.deriveNewAbstraction(
									source.getAccessPath(), stmt));
							if (abs != null)
								res.add(abs);
						}

						// checks: this/fields
						Value sourceBase = source.getAccessPath().getPlainValue();
						if (!isExecutorExecute
								&& !source.getAccessPath().isStaticFieldRef()
								&& !dest.isStatic()) {
							InstanceInvokeExpr iIExpr = (InstanceInvokeExpr) stmt.getInvokeExpr();
							Value callBase = isReflectiveCallSite ? iIExpr.getArg(0) : iIExpr.getBase();
							
							if (callBase == sourceBase && manager.getTypeUtils().hasCompatibleTypesForCall(
									source.getAccessPath(), dest.getDeclaringClass())) {
								boolean param = false;
								// check if it is not one of the params (then we have already fixed it)
								if (!isReflectiveCallSite) {
									for (int i = 0; i < dest.getParameterCount(); i++) {
										if (stmt.getInvokeExpr().getArg(i) == sourceBase) {
											param = true;
											break;
										}
									}
								}
								
								// Map the base local into the callee
								if (!param) {
									AccessPath ap = manager.getAccessPathFactory().copyWithNewValue(
											source.getAccessPath(), thisLocal);
									Abstraction abs = checkAbstraction(source.deriveNewAbstraction(ap, (Stmt) src));
									if (abs != null) {
										for(Unit sp : manager.getICFG().getStartPointsOf(dest)) {
											res.add(useValueTofindCallInfo(thisLocal, sp, abs));
										}
									}
										//res.add(abs);
								}
							}
						}
						
						// Map the parameter values into the callee
						if (isExecutorExecute) {
							if (ie.getArg(0) == source.getAccessPath().getPlainValue()) {
								AccessPath ap = manager.getAccessPathFactory().copyWithNewValue(
										source.getAccessPath(), thisLocal);
								Abstraction abs = checkAbstraction(source.deriveNewAbstraction(ap, stmt));
								if (abs != null) {
									for(Unit sp : manager.getICFG().getStartPointsOf(dest)) {
										res.add(useValueTofindCallInfo(thisLocal, sp, abs));
									}
								}
									//res.add(abs);
							}
						}
						else if (ie != null && dest.getParameterCount() > 0) {
							assert dest.getParameterCount() == ie.getArgCount();
							// check if param is tainted:
							for (int i = isReflectiveCallSite ? 1 : 0; i < ie.getArgCount(); i++) {
								if (ie.getArg(i) == source.getAccessPath().getPlainValue()) {
									
									if (isReflectiveCallSite) {
										// If we have a reflective method call and the argument array is
										// tainted, we taint all parameters
										for (int j = 0; i < paramLocals.length; i++) {
											AccessPath ap = manager.getAccessPathFactory().copyWithNewValue(
													source.getAccessPath(), paramLocals[j], null, false);
											Abstraction abs = checkAbstraction(source.deriveNewAbstraction(ap, stmt));
											if (abs != null) {
												for(Unit sp : manager.getICFG().getStartPointsOf(dest)) {
													res.add(useValueTofindCallInfo(paramLocals[j], sp, abs));
												}
											}
												//res.add(abs);
										}
									}
									else {
										// Taint the respective parameter local
										AccessPath ap = manager.getAccessPathFactory().copyWithNewValue(
												source.getAccessPath(), paramLocals[i]);
										Abstraction abs = checkAbstraction(source.deriveNewAbstraction(ap, stmt));
										if (abs != null) {
											for(Unit sp : manager.getICFG().getStartPointsOf(dest)) {
												res.add(useValueTofindCallInfo(paramLocals[i], sp, abs));
											}

										}
									}
								}
							}
						}
						
						// Inject our calling context into the other solver
						if (res != null && !res.isEmpty())
							for (Abstraction d3 : res)
								manager.getForwardSolver().injectContext(solver, dest, d3, src, source, d1);
						
						return notifyOutFlowHandlers(src, d1, source, res,
								FlowFunctionType.CallFlowFunction);
					}
				};
			}


			public Abstraction useValueTofindCallInfo(Value value, Unit stmt, Abstraction abs) {

				DataFlowNode dataFlowNode = DataFlowGraphQuery.v().useValueTofindBackwardDataFlowGraph(value, stmt, false);

				return dataFlowNode.deriveNewAbsAllInfo(abs);

			}



			@Override
			public FlowFunction<Abstraction> getReturnFlowFunction(final Unit callSite, final SootMethod callee,
					final Unit exitStmt, final Unit retSite) {
				final Value[] paramLocals = new Value[callee.getParameterCount()]; 
				for (int i = 0; i < callee.getParameterCount(); i++)
					paramLocals[i] = callee.getActiveBody().getParameterLocal(i);
				
				final Stmt stmt = (Stmt) callSite;
				final InvokeExpr ie = (stmt != null && stmt.containsInvokeExpr())
						? stmt.getInvokeExpr() : null;
				final boolean isReflectiveCallSite = interproceduralCFG().isReflectiveCallSite(ie);
				
				// This is not cached by Soot, so accesses are more expensive
				// than one might think
				final Local thisLocal = callee.isStatic() ? null : callee.getActiveBody().getThisLocal();
				
				// Android executor methods are handled specially. getSubSignature()
				// is slow, so we try to avoid it whenever we can
				final boolean isExecutorExecute = interproceduralCFG().isExecutorExecute(ie, callee);
				
				return new SolverReturnFlowFunction() {
					
					@Override
					public Set<Abstraction> computeTargets(Abstraction source,
							Abstraction d1,
							Collection<Abstraction> callerD1s) {
						if (source == getZeroValue())
							return Collections.emptySet();
						assert source.isAbstractionActive() || manager.getConfig().getFlowSensitiveAliasing();
						
						// If we have no caller, we have nowhere to propagate. This
						// can happen when leaving the main method.
						if (callSite == null)
							return Collections.emptySet();
						
						// Notify the handler if we have one
						if (taintPropagationHandler != null)
							taintPropagationHandler.notifyFlowIn(stmt, source, interproceduralCFG(),
									FlowFunctionType.ReturnFlowFunction);
												
						// easy: static
						if (manager.getConfig().getEnableStaticFieldTracking()
								&& source.getAccessPath().isStaticFieldRef()) {
							registerActivationCallSite(callSite, callee, source);
							return notifyOutFlowHandlers(exitStmt, d1, source, Collections.singleton(source),
									FlowFunctionType.ReturnFlowFunction);
						}

						final Value sourceBase = source.getAccessPath().getPlainValue();
						Set<Abstraction> res = new HashSet<Abstraction>();
						
						// Since we return from the top of the callee into the
						// caller, return values cannot be propagated here. They
						// don't yet exist at the beginning of the callee.
						
						if (isExecutorExecute) {
							// Map the "this" object to the first argument of the call site
							if (source.getAccessPath().getPlainValue() == thisLocal) {
								AccessPath ap = manager.getAccessPathFactory().copyWithNewValue(
										source.getAccessPath(), ie.getArg(0));
								Abstraction abs = checkAbstraction(source.deriveNewAbstraction(ap, (Stmt) exitStmt));
								if (abs != null) {
									res.add(useValueTofindCallInfo(ie.getArg(0), callSite, abs));
									//res.add(abs);
									registerActivationCallSite(callSite, callee, abs);
								}
							}
						}
						else {
							boolean parameterAliases = false;
							
							// check one of the call params are tainted (not if simple type)
							for (int i = 0; i < paramLocals.length; i++) {
								if (paramLocals[i] == sourceBase) {
									parameterAliases = true;
									if (callSite instanceof Stmt) {
										Value originalCallArg = ie.getArg(isReflectiveCallSite ? 1 : i);
										
										// If this is a constant parameter, we can safely ignore it
										if (!AccessPath.canContainValue(originalCallArg))
											continue;
										if (!isReflectiveCallSite && !manager.getTypeUtils().checkCast(
												source.getAccessPath(), originalCallArg.getType()))
											continue;
										
										// Primitive types and strings cannot have aliases and thus
										// never need to be propagated back
										if (source.getAccessPath().getBaseType() instanceof PrimType)
											continue;
										if (TypeUtils.isStringType(source.getAccessPath().getBaseType())
												&& !source.getAccessPath().getCanHaveImmutableAliases())
											continue;
										
										// If the variable was overwritten somewehere in the callee, we assume it
										// to overwritten on all paths (yeah, I know ...) Otherwise, we need SSA
										// or lots of bookkeeping to avoid FPs (BytecodeTests.flowSensitivityTest1).
										if (interproceduralCFG().methodWritesValue(callee, paramLocals[i]))
											continue;

										AccessPath ap = manager.getAccessPathFactory().copyWithNewValue(
												source.getAccessPath(), originalCallArg,
												isReflectiveCallSite ? null : source.getAccessPath().getBaseType(),
												false);
										Abstraction abs = checkAbstraction(source.deriveNewAbstraction(
												ap, (Stmt) exitStmt));

										if (abs != null) {
											res.add(useValueTofindCallInfo(originalCallArg, callSite, abs));
											//res.add(abs);
											registerActivationCallSite(callSite, callee, abs);
										}
									}
								}
							}
							
							// Map the "this" local
							if (!callee.isStatic()) {
								if (thisLocal == sourceBase && manager.getTypeUtils().hasCompatibleTypesForCall(
										source.getAccessPath(), callee.getDeclaringClass())) {
									// check if it is not one of the params (then we have already fixed it)
									if (!parameterAliases) {
										if (callSite instanceof Stmt) {
											Stmt stmt = (Stmt) callSite;
											if (stmt.getInvokeExpr() instanceof InstanceInvokeExpr) {
												InstanceInvokeExpr iIExpr = (InstanceInvokeExpr) stmt.getInvokeExpr();
												Value callerBaseLocal = interproceduralCFG().isReflectiveCallSite(iIExpr)
														? iIExpr.getArg(0) : iIExpr.getBase();
												
												AccessPath ap = manager.getAccessPathFactory().copyWithNewValue(
														source.getAccessPath(), callerBaseLocal,
														isReflectiveCallSite ? null : source.getAccessPath().getBaseType(),
														false);
												Abstraction abs = checkAbstraction(source.deriveNewAbstraction(
														ap, (Stmt) exitStmt));
												if (abs != null) {
													res.add(useValueTofindCallInfo(iIExpr.getBase(), callSite, abs));

													//res.add(abs);
													registerActivationCallSite(callSite, callee, abs);
												}
											}
										}
									}
								}
								}
						}
																		
						for (Abstraction abs : res)
							if (abs != source)
								abs.setCorrespondingCallSite((Stmt) callSite);
						
						return notifyOutFlowHandlers(exitStmt, d1, source, res,
								FlowFunctionType.ReturnFlowFunction);
					}
				};
			}
			
			@Override
			public FlowFunction<Abstraction> getCallToReturnFlowFunction(final Unit call, final Unit returnSite) {
				final Stmt iStmt = (Stmt) call;
				final InvokeExpr invExpr = iStmt.getInvokeExpr();
				
				final Value[] callArgs = new Value[iStmt.getInvokeExpr().getArgCount()];
				for (int i = 0; i < iStmt.getInvokeExpr().getArgCount(); i++)
					callArgs[i] = iStmt.getInvokeExpr().getArg(i);
				
				final SootMethod callee = invExpr.getMethod();
				
				final DefinitionStmt defStmt = iStmt instanceof DefinitionStmt
						? (DefinitionStmt) iStmt : null;
				
				return new SolverCallToReturnFlowFunction() {
					@Override
					public Set<Abstraction> computeTargets(Abstraction d1, Abstraction source) {
						if (source == getZeroValue())
							return Collections.emptySet();
						assert source.isAbstractionActive() || manager.getConfig().getFlowSensitiveAliasing();
						
						// Notify the handler if we have one
						if (taintPropagationHandler != null)
							taintPropagationHandler.notifyFlowIn(call, source, interproceduralCFG(),
									FlowFunctionType.CallToReturnFlowFunction);
						
						// Compute wrapper aliases
						if (taintWrapper != null) {
							Set<Abstraction> wrapperAliases = taintWrapper.getAliasesForMethod(
									iStmt, d1, source);
							if (wrapperAliases != null && !wrapperAliases.isEmpty()) {
								Set<Abstraction> passOnSet = new HashSet<>(wrapperAliases.size());
								for (Abstraction abs : wrapperAliases)
									if (defStmt != null && defStmt.getLeftOp()
											== abs.getAccessPath().getPlainValue()) {
										// Do not pass on this taint, but trigger the forward analysis

										Set<Unit> nextSet = getNextStmtFromForwardDfg(defStmt.getLeftOp(), defStmt, abs);
										for (Unit u : nextSet)
											manager.getForwardSolver().processEdge(new PathEdge<Unit, Abstraction>(d1, u, abs));


//										for (Unit u : interproceduralCFG().getPredsOf(defStmt))
//											manager.getForwardSolver().processEdge(new PathEdge<Unit, Abstraction>(d1, u, abs));
									}
									else
										passOnSet.add(abs);

								Set<Abstraction> newPassSet = new HashSet<>();

								for(Abstraction abs : passOnSet) {
									newPassSet.add(getAbsFromBackwardDfg(abs.getAccessPath().getPlainValue(),
											defStmt, abs));

								}
								
								return notifyOutFlowHandlers(call, d1, source, newPassSet,
										FlowFunctionType.CallToReturnFlowFunction);
							}
						}
						
						// Additional check: If all callees are library
						// classes, we pass it on as well
						boolean mustPropagate = isExcluded(callee);
						
						// If the callee does not read the given value, we also need to pass it on
						// since we do not propagate it into the callee.
						if (!mustPropagate
								&& manager.getConfig().getEnableStaticFieldTracking()
								&& source.getAccessPath().isStaticFieldRef()) {
							if (interproceduralCFG().isStaticFieldUsed(callee,
									source.getAccessPath().getFirstField()))
								return Collections.emptySet();
						}
						
						// We may not pass on a taint if it is overwritten by this call
						if (iStmt instanceof DefinitionStmt && ((DefinitionStmt) iStmt).getLeftOp()
								== source.getAccessPath().getPlainValue())
							return Collections.emptySet();
						
						// If the base local of the invocation is tainted, we do not
						// pass on the taint
						if (!mustPropagate && iStmt.getInvokeExpr() instanceof InstanceInvokeExpr) {
							InstanceInvokeExpr iinv = (InstanceInvokeExpr) iStmt.getInvokeExpr();
							if (iinv.getBase() == source.getAccessPath().getPlainValue()
									&& !interproceduralCFG().getCalleesOfCallAt(call).isEmpty())
								return Collections.emptySet();
						}
						
						// We do not pass taints on parameters over the call-to-return edge
						if (!mustPropagate) {
							for (int i = 0; i < callArgs.length; i++)
								if (callArgs[i] == source.getAccessPath().getPlainValue())
									return Collections.emptySet();
						}

						 Abstraction newabs = getAbsFromBackwardDfg(source.getAccessPath().getPlainValue(),
								iStmt, source);
												
						return notifyOutFlowHandlers(call, d1, source, Collections.singleton(newabs),
								FlowFunctionType.CallToReturnFlowFunction);
					}
				};
			}
			
		};
	}
	
}
