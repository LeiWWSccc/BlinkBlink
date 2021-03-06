package soot.jimple.infoflow.sparseOptimization.dataflowgraph.function;

import heros.solver.Pair;
import soot.SootField;
import soot.Value;
import soot.jimple.IdentityStmt;
import soot.jimple.infoflow.Infoflow;
import soot.jimple.infoflow.sparseOptimization.dataflowgraph.BaseInfoStmt;
import soot.jimple.infoflow.sparseOptimization.dataflowgraph.data.DFGEntryKey;
import soot.jimple.infoflow.sparseOptimization.dataflowgraph.data.DataFlowNode;
import soot.jimple.infoflow.sparseOptimization.dataflowgraph.data.DataFlowNodeFactory;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * @author wanglei
 */
public class BackwardFunction extends AbstractFunction {

    BackwardFunction(Map<Pair<BaseInfoStmt, DataFlowNode>, DataFlowNode > visited,
                     Set<Value> parmAndThis,
                     Map<DFGEntryKey, Pair<BaseInfoStmt, DataFlowNode>> seed,
                     HashMap<Pair<BaseInfoStmt, BaseInfoStmt>, Set<Integer>> reachableMap) {
        super(visited, parmAndThis, seed, reachableMap);
    }

    public Set<Pair<BaseInfoStmt, DataFlowNode>> flowFunction(BaseInfoStmt target, BaseInfoStmt src, DataFlowNode source) {
        Set<Pair<BaseInfoStmt, DataFlowNode>> res = new HashSet<>();


        if(target.base == null && !target.isHead) {
            addResult(res, target, source);
            return res;
        }
        if (target.base == null) {
            //return
            if(canNodeReturn(source.getValue())) {
                DataFlowNode returnNode = DataFlowNodeFactory.v().createDataFlowNode(target.stmt, target.base, null, false);
                returnNode = getNewDataFlowNode(target, returnNode);
                source.setSuccs(DataFlowNode.baseField, returnNode, null);
            }
            //res.add(newNode);
            return res;
        }

        SootField baseField = DataFlowNode.baseField;

        SootField sourceField = source.getField();

        SootField targetLeftField = target.leftField;
        SootField[] targetRightFields = target.rightFields;
        SootField[] targetArgFields = target.argsFields;

        boolean isKillSource = false;
        DataFlowNode newNode = null;

        if (sourceField != baseField) {
            //(1) source like  :  a.f1

            //a = b;   gen  b.f
            //a.f1 = xxx;

            //a.f1 = b;
            //a.f1 =

            if (targetLeftField != null) {
                //(1.1) like  a =  xxx; or  a.f1 = xxx; or a.f2 = xxx;

                if (targetLeftField == baseField ) {
                    //(1.1.1) a = xxx;  source : a.f1 , gen f1 -> <a>
                    // a = b;
                    // a.f1 = pwd;  or alias = a.f1  ;

                    newNode = DataFlowNodeFactory.v().createDataFlowNode(target.stmt, target.base, targetLeftField, true);
                    newNode = getNewDataFlowNode(target, newNode);
                    source.setSuccs(sourceField, newNode, null);
                    //res.add(newNode);
                    if(!(target.stmt instanceof IdentityStmt))
                         isKillSource = true;
                    /* //fix bug, version 2
                       a = c;
                       a = b;
                       a.f1 = source();
                       c.f should not be tainted!
                    */

                }else if(targetLeftField.equals(sourceField)) {
                    //(1.1.2) a.f1 = xxx; source : a.f1  , gen f1 -> <a.f1>
                    // a.f1 = b;
                    // a.f1 = pwd;
                    newNode = DataFlowNodeFactory.v().createDataFlowNode(target.stmt, target.base, targetLeftField, true);
                    newNode = getNewDataFlowNode(target, newNode);
                    source.setSuccs(sourceField, newNode, null);
                   // source.setKillField(targetLeftField);
                    // TODO
                    if(!(target.stmt instanceof IdentityStmt))
                        isKillSource = true;


                }  else {
                    //(1.1.3) a.f2 = xxx;  source : a.f1, do nothing.

                    //a.f2 = b;
                    //a.f1 = pwd;
                    if(Infoflow.isFlowDroidSameRule) {

                        isKillSource = true;

                        newNode = DataFlowNodeFactory.v().createDataFlowNode
                                (target.stmt, source.getValue(), baseField, true);
                        newNode = getNewDataFlowNode(target, newNode);

                        source.setSuccs(sourceField, newNode, null);


                        Pair<BaseInfoStmt, DataFlowNode> path = new Pair<BaseInfoStmt, DataFlowNode>(target, newNode);

                        seed.put(new DFGEntryKey(target.stmt, source.getValue(), baseField, false), path);
                        addResult(res, path);

                    }
                }

            }

            if (targetRightFields != null) {
                //(1.2) like : xxx = a; or xxx = a.f1; or xxx = a.f2;
                if(targetRightFields.length != 1) {
                    throw new RuntimeException("Sparse Op: Alias analysis should't at two or more rightOP ");
                }

                SootField right = targetRightFields[0];

                if (right == baseField || sourceField.equals(right)) {
                    //(1.2.1) xxx = a;  source : a.f1
                    //(1.2.2) xxx = a.f1;   source : a.f1
                    newNode = DataFlowNodeFactory.v().createDataFlowNode(target.stmt, target.base, right, false);
                    newNode = getNewDataFlowNode(target, newNode);
                    source.setSuccs(sourceField, newNode, null);
                    //res.add(newNode);
                } else {
                    //(1.2.3) xxx = a.f2; source : a.f1  , do nothing.
                }

            }

            if (targetArgFields != null) {
                for (int i = 0; i < targetArgFields.length; i++) {
                    SootField arg = targetArgFields[i];
                    if (arg == baseField) {
                        //(1.3.1) foo(a);    source : a.f1 , gen new a.f1
                        newNode = DataFlowNodeFactory.v().createDataFlowNode(target.stmt, target.base, arg, false);
                        newNode = getNewDataFlowNode(target, newNode);
                        source.setSuccs(sourceField, newNode, null);
                        //res.add(newNode);
                        isKillSource = true;

                    } else if (arg.equals(sourceField)) {
                        //(1.3.2) foo(a.f1); source : a.f1  , gen new a.f1
                        newNode = DataFlowNodeFactory.v().createDataFlowNode(target.stmt, target.base, arg, false);
                        newNode = getNewDataFlowNode(target, newNode);
                        source.setSuccs(sourceField, newNode, null);
                        isKillSource = true;
                        //res.add(newNode);
                    } else {
                        isKillSource = true;

                        //(1.3.3) foo(a.f2); source : a.f1, do nothing.

                    }
                }
            }

        } else if (sourceField != null) {
            //(2) source like  :  a

            if (targetLeftField != null) {
                //(2.1) like  a =  xxx; or  a.f1 = xxx; or a.f2 = xxx;

                if (targetLeftField == baseField) {
                    // a = xxx;    source : a , gen new a

                    // a = c;

                    // a = b;   kill source
                    // source(a);

                    newNode = DataFlowNodeFactory.v().createDataFlowNode(target.stmt, target.base, targetLeftField, true);
                    newNode = getNewDataFlowNode(target, newNode);
                    source.setSuccs(sourceField, newNode, null);
                    if(!(target.stmt instanceof IdentityStmt))
                        isKillSource = true;

                } else {
                    //(1) a.f1 = xxx ; source : a  , gen new a.f1

                    // a = b;
                    // a.f1 = xxx;
                    // source(a);

                    newNode = DataFlowNodeFactory.v().createDataFlowNode(target.stmt, target.base, targetLeftField, true);
                    newNode = getNewDataFlowNode(target, newNode);
                    source.setSuccs(sourceField, newNode, null);
                    //isKillSource = true;


                    isKillSource = true;

                    newNode = DataFlowNodeFactory.v().createDataFlowNode
                            (target.stmt, source.getValue(), source.getField(), true);
                    newNode = getNewDataFlowNode(target, newNode);
//                    //source.setSuccs(sourceField, newNode);
//                    setSuccs(sourceField, source, newNode, src, target, true);

                    Pair<BaseInfoStmt, DataFlowNode> path = new Pair<BaseInfoStmt, DataFlowNode>(target, newNode);

                    seed.put(new DFGEntryKey(target.stmt, source.getValue(), source.getField(), false), path);
                    // seed.add(new Pair<VariableInfo, DataFlowNode>(baseInfo, dataFlowNode));
                    addResult(res, path);

                }

            }

            if (targetRightFields != null) {
                //like xxx = a;  or xxx = a.f1 ;

                if(targetRightFields.length != 1) {
                    throw new RuntimeException("Sparse Op: Alias analysi should't at two or more rightOP ");
                }

                SootField right = targetRightFields[0];

                if (right == baseField) {
                    // xxx = a;   source : a , kill source

                    // c = a;

                    // b = a;
                    // source(a);

                    newNode = DataFlowNodeFactory.v().createDataFlowNode(target.stmt, target.base, right, false);
                    newNode = getNewDataFlowNode(target, newNode);
                    source.setSuccs(right, newNode, null);

                } else {
                    // xxx = a.f1  or xxx = a.f2; source : a ,  just kill field f1.


                    newNode = DataFlowNodeFactory.v().createDataFlowNode(target.stmt, target.base, right, false);
                    newNode = getNewDataFlowNode(target, newNode);
                    source.setSuccs(right, newNode, null);
                    // b = a.f1
                    // source(a);  if source = a.f1  strong update !!!

                    // b = a.f2;
                    // source(a);  if source = a.f1  no strong update

                }
            }

            if (targetArgFields != null) {
                for (int i = 0; i < targetArgFields.length; i++) {
                    SootField arg = targetArgFields[i];
                    if (arg == baseField) {
                        // foo(a);    source : a , gen "base" -> <a>
                        newNode = DataFlowNodeFactory.v().createDataFlowNode(target.stmt, target.base, arg, false);
                        newNode = getNewDataFlowNode(target, newNode);
                        source.setSuccs(arg, newNode, null);

                        isKillSource = true;

                    } else if (arg.equals(sourceField)) {
                        // foo(a.f1); source : a , gen f1 -> <a.f1>
                        newNode = DataFlowNodeFactory.v().createDataFlowNode(target.stmt, target.base, arg, false);
                        newNode = getNewDataFlowNode(target, newNode);
                        source.setSuccs(arg, newNode, null);
                        isKillSource = true;
                    }
                }
            }

        } else {
            throw new RuntimeException("source's base field can not be null ");
        }

        if (!isKillSource)
            addResult(res, target, source);
        return res;

    }
}
