import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import soot.AntTask.PhaseOptbb;
import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.PackManager;
import soot.PatchingChain;
import soot.PhaseOptions;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Transform;
import soot.Unit;
import soot.jimple.AbstractStmtSwitch;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.StringConstant;
import soot.options.Options;
import soot.toDex.DexPrinter;


public class AndroidInstrument {
	
	private static String[] stripDuplicateAndroidJarsBug(final String[] args) {
		List<String> argList = new ArrayList<>();
		for (int i = 0; i < args.length; i++) {
			if ("-android-jars".equals(args[i])) {
				i++;
			}
			else {
				argList.add(args[i]);
			}
		}
		return argList.toArray(new String[argList.size()]);
	}
	
	public static void main(String[] args) {
		//prefer Android APK files// -src-prec apk
		Options.v().set_src_prec(Options.src_prec_apk);
		//output as APK, too//-f J
		Options.v().set_output_format(Options.output_format_dex);
		Options.v().parse(args);

        SootClass c = Scene.v().forceResolve("br.com.lealdn.client.ClientMain", SootClass.BODIES);
        c.setApplicationClass();
        Scene.v().loadNecessaryClasses();
        
		for (final SootClass clazz : Scene.v().getClasses()) {
			for (final SootMethod method : clazz.getMethods()) {
				if (SootUtils.isAnnotated(method)) {
					SootUtils.modifyMethodToOffload(method);
				}
			}
		}
		
		PackManager.v().writeOutput();
	}
	

    private static Local addTmpRef(Body body)
    {
        Local tmpRef = Jimple.v().newLocal("tmpRef", RefType.v("java.io.PrintStream"));
        body.getLocals().add(tmpRef);
        return tmpRef;
    }
    
    private static Local addTmpString(Body body)
    {
        Local tmpString = Jimple.v().newLocal("tmpString", RefType.v("java.lang.String")); 
        body.getLocals().add(tmpString);
        return tmpString;
    }
}
