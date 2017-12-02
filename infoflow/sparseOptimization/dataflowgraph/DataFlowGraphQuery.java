package soot.jimple.infoflow.sparseOptimization.dataflowgraph;

import heros.solver.Pair;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.infoflow.sparseOptimization.basicblock.BasicBlockGraph;
import soot.jimple.infoflow.sparseOptimization.dataflowgraph.data.DFGEntryKey;
import soot.jimple.infoflow.sparseOptimization.dataflowgraph.data.DataFlowNode;

import java.util.Map;

/**
 * @author wanglei
 */
public class DataFlowGraphQuery {


    public static DataFlowGraphQuery instance = null;

    final private IInfoflowCFG iCfg;

    final private  Map<SootMethod, Map<Value, Map<DFGEntryKey, Pair<BaseInfoStmt, DataFlowNode>>>> dfg ;

    final private  Map<SootMethod, Map<Value, Map<DFGEntryKey, Pair<BaseInfoStmt, DataFlowNode>>>> backwardDfg ;


    public static DataFlowGraphQuery v() {
        if(instance == null)
            throw new RuntimeException("DataFlowGraphQuery doesn't initialize!");
        return instance;}

    DataFlowGraphQuery(IInfoflowCFG iCfg,
                       Map<SootMethod, Map<Value, Map<DFGEntryKey, Pair<BaseInfoStmt, DataFlowNode>>>> dfg,
                       Map<SootMethod, Map<Value, Map<DFGEntryKey, Pair<BaseInfoStmt, DataFlowNode>>>> backwardDfg) {
        this.iCfg = iCfg;
        this.dfg = dfg;
        this.backwardDfg = backwardDfg;
    }

    public static void initialize(IInfoflowCFG iCfg,
                                  Map<SootMethod, Map<Value, Map<DFGEntryKey, Pair<BaseInfoStmt, DataFlowNode>>>> dfg,
                                  Map<SootMethod, Map<Value, Map<DFGEntryKey, Pair<BaseInfoStmt, DataFlowNode>>>> backwardDfg) {
        instance = new DataFlowGraphQuery(iCfg, dfg, backwardDfg);

    }

    public DataFlowNode useApTofindDataFlowGraph(AccessPath ap, Unit stmt) {
        SootMethod caller = iCfg.getMethodOf(stmt);
        Value base = ap.getPlainValue();
        SootField field1 = ap.getFirstField();
        if(field1 == null)
            field1 = DataFlowNode.baseField;

        DFGEntryKey key = new DFGEntryKey(stmt, base, field1);

        if(!dfg.containsKey(caller)) return null;
        Map<Value, Map<DFGEntryKey, Pair<BaseInfoStmt, DataFlowNode>>> l1 = dfg.get(caller);
        if(!l1.containsKey(base)) return null;
        Map<DFGEntryKey, Pair<BaseInfoStmt, DataFlowNode>> l2 = l1.get(base);
        if(!l2.containsKey(key)) return null;
        Pair<BaseInfoStmt, DataFlowNode> pair = l2.get(key);
        if(pair == null) return null;

        return pair.getO2();
    }

    public DataFlowNode useValueTofindBackwardDataFlowGraph(Value value, Unit stmt) {
        return useValueTofindBackwardDataFlowGraph(value, stmt, true);
    }

    public DataFlowNode useValueTofindBackwardDataFlowGraph(Value value, Unit stmt, boolean isOriginal) {
        Pair<Value, SootField> pair = BasicBlockGraph.getBaseAndField(value);
        return useBaseAndFieldTofindDataFlowGraph(pair.getO1(), pair.getO2(), stmt, isOriginal, false);
    }

    public DataFlowNode useBaseTofindBackwardDataFlowGraph(Value base, Unit stmt, boolean isOriginal) {
        return useBaseAndFieldTofindDataFlowGraph(base, null, stmt, isOriginal, false);
    }

    public DataFlowNode useBaseTofindBackwardDataFlowGraph(Value base, Unit stmt ) {
        return useBaseTofindBackwardDataFlowGraph(base, stmt, true);
    }





    public  DataFlowNode useBaseAndFieldTofindDataFlowGraph(Value base, SootField field, Unit stmt, boolean isOriginal, boolean isForward) {
        Map<SootMethod, Map<Value, Map<DFGEntryKey, Pair<BaseInfoStmt, DataFlowNode>>>> dfg;
        if(isForward)
            dfg = this.dfg;
        else
            dfg = this.backwardDfg;

        SootMethod caller = iCfg.getMethodOf(stmt);
        if(field == null)
            field = DataFlowNode.baseField;

        DFGEntryKey key = new DFGEntryKey(stmt, base, field, isOriginal);

        if(!dfg.containsKey(caller)) return null;
        Map<Value, Map<DFGEntryKey, Pair<BaseInfoStmt, DataFlowNode>>> l1 = dfg.get(caller);
        if(!l1.containsKey(base)) return null;
        Map<DFGEntryKey, Pair<BaseInfoStmt, DataFlowNode>> l2 = l1.get(base);
        if(!l2.containsKey(key)) return null;
        Pair<BaseInfoStmt, DataFlowNode> pair = l2.get(key);
        if(pair == null) return null;

        return pair.getO2();
    }

    public DataFlowNode useValueTofindForwardDataFlowGraph(Value value, Unit stmt) {
        return useValueTofindForwardDataFlowGraph(value, stmt, true);
    }

    public DataFlowNode useValueTofindForwardDataFlowGraph(Value value, Unit stmt, boolean isOriginal) {
        Pair<Value, SootField> pair = BasicBlockGraph.getBaseAndField(value);
        return useBaseAndFieldTofindDataFlowGraph(pair.getO1(), pair.getO2(), stmt, isOriginal, true);
    }

    public DataFlowNode useBaseTofindForwardDataFlowGraph(Value base, Unit stmt, boolean isOriginal) {
        return useBaseAndFieldTofindDataFlowGraph(base, null, stmt, isOriginal, true);
    }

    public DataFlowNode useBaseTofindForwardDataFlowGraph(Value base, Unit stmt ) {
        return useBaseTofindForwardDataFlowGraph(base, stmt, true);
    }


}
