package soot.jimple.infoflow.sparseOptimization.dataflowgraph.function;

import heros.solver.Pair;
import soot.Value;
import soot.jimple.infoflow.sparseOptimization.dataflowgraph.BaseInfoStmt;
import soot.jimple.infoflow.sparseOptimization.dataflowgraph.data.DFGEntryKey;
import soot.jimple.infoflow.sparseOptimization.dataflowgraph.data.DataFlowNode;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * @author wanglei
 */
public class FunctionFactory {

    public static AbstractFunction getFunction(boolean isForward, Map<Pair<BaseInfoStmt, DataFlowNode>,DataFlowNode > visited,
                                               Set<Value> parmAndThis,
                                               Map<DFGEntryKey, Pair<BaseInfoStmt, DataFlowNode>> seed,
                                               HashMap<Pair<BaseInfoStmt, BaseInfoStmt>, Set<Integer>> reachableMap) {
        if(isForward)
            return new ForwardFunction(visited, parmAndThis, seed, reachableMap);
        else
            return new BackwardFunction(visited, parmAndThis, seed, reachableMap);
    }
//
//    public static AbstractFunction getFunction(boolean isForward, Map<Pair<BaseInfoStmt, DataFlowNode>,DataFlowNode > backwardSeed , Map<Pair<BaseInfoStmt, DataFlowNode>,DataFlowNode > visited) {
//        if(isForward)
//            return new ForwardFunction(visited, backwardSeed);
//        else
//            return new BackwardFunction(visited);
//    }
}
