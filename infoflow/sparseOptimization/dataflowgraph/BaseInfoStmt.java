package soot.jimple.infoflow.sparseOptimization.dataflowgraph;

import soot.SootField;
import soot.Value;
import soot.jimple.Stmt;
import soot.jimple.infoflow.sparseOptimization.basicblock.BasicBlock;

import java.util.Set;

/**
 * @author wanglei
 */
public class BaseInfoStmt {

    public BasicBlock bb;
    public int idx ;
    public Value base;
    public Stmt stmt;
    public boolean isHead;

    public SootField leftField;
    public SootField[] rightFields;
    public SootField[] argsFields;

    public BaseInfoStmt(boolean isHead, Value base, SootField left, SootField[] rightFields, SootField[] argsFields, BasicBlock bb, int i, Stmt s) {
        this.isHead = isHead;
        this.base = base;
        this.leftField = left;
        this.rightFields = rightFields;
        this.argsFields = argsFields;
        this.bb = bb;
        this.idx = i;
        this.stmt = s;
    }

    public Set<BaseInfoStmt> Succs = null;
    public Set<BaseInfoStmt> Preds = null;

    @Override
    public String toString() {
        if(base == null) {
            if(isHead)
                return "ENTRY STMT : " + stmt;
            else
                return "EXIT STMT : " + stmt;

        }

        return "STMT{ " + stmt + " }, [Base : " + base + "]";
    }

}