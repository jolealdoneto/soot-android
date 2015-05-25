


import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.lang.model.type.ArrayType;

import soot.Body;
import soot.BooleanType;
import soot.ByteType;
import soot.CharType;
import soot.DoubleType;
import soot.FloatType;
import soot.IntType;
import soot.Local;
import soot.LongType;
import soot.Modifier;
import soot.PatchingChain;
import soot.RefLikeType;
import soot.RefType;
import soot.Scene;
import soot.ShortType;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.VoidType;
import soot.jimple.AssignStmt;
import soot.jimple.Constant;
import soot.jimple.DoubleConstant;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;
import soot.jimple.ReturnStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.StringConstant;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JStaticInvokeExpr;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.tagkit.AnnotationTag;
import soot.tagkit.Tag;
import soot.tagkit.VisibilityAnnotationTag;

public class SootUtils {
    public static void modifyMethodToOffload(final SootMethod method) {
    	method.getDeclaringClass().setApplicationClass();
        final List<SootField> staticFields = getStaticFieldsFromMethod(method, new HashSet<SootMethod>());
        final Body body = method.retrieveActiveBody();
        System.out.println("Fields:");
        System.out.println(staticFields);
        turnFieldsPublic(staticFields);
        
        final SootMethod copyMethod = copyMethod(method);
        Unit cursor = stripAllUnitsFromMethod(body);
        cursor = body.getUnits().getLast();
        final Unit noop = Jimple.v().newNopStmt();
        body.getUnits().add(noop);

        final Map<String, Object> mapResult = addMapToBody(body, cursor);
        final Local mapLocal = (Local)mapResult.get("mapLocal");
        final Local startTimeLocal = createStartTimeLocal(body);
        cursor = (Unit)mapResult.get("cursor");
        
        for (final SootField f : staticFields) {
            cursor = addLocalForFieldAndAddToMap(f, body, mapLocal, cursor);
        }

        cursor = addThisRefToMap(mapLocal, body, cursor);
        cursor = addArgsRefToMap(mapLocal, body, method, cursor);
        cursor = invokeConditionToOffloadIfNecessary(method, mapLocal, startTimeLocal, body, cursor);
        final Unit[] cursorAndTrapStmt = invokeInterceptorWithNeededLocals(method, mapLocal, body, cursor);
        cursor = cursorAndTrapStmt[0];
        addCallsToInstrumentingMethod(method, body, cursor, copyMethod, startTimeLocal, mapLocal, cursorAndTrapStmt[1]);
        
        body.getUnits().remove(noop);
        
        System.out.println(body);
    }
    
    private static Unit stripAllUnitsFromMethod(final Body body) {
    	final JimpleBody jbody = (JimpleBody)body;
    	List<Value> paramRefs = jbody.getParameterRefs();
    	List<Unit> unitsToRemove = new ArrayList<Unit>();
    	Unit suc = jbody.getFirstNonIdentityStmt();
    	Unit last = suc;
    	while(suc != null) {
    		if (!paramRefs.contains(suc)) {
    			unitsToRemove.add(suc);
    		}
    		suc = body.getUnits().getSuccOf(suc);
    	}
    	
    	for (Unit toRemove : unitsToRemove) {
    		body.getUnits().remove(toRemove);
    	}
    	
    	return last;
    }
    
    private static SootMethod copyMethod(final SootMethod method) {
    	final SootMethod copy = new SootMethod("$offloadCopy_" + method.getName(), method.getParameterTypes(), method.getReturnType(), method.getModifiers());
    	final JimpleBody copyBody = Jimple.v().newBody(copy);
    	copy.setActiveBody(copyBody);
    	final Body methodBody = method.retrieveActiveBody();
    	method.getDeclaringClass().addMethod(copy);
    	copyBody.importBodyContentsFrom(methodBody);

    	for (final Unit unit : copyBody.getUnits()) {
    		cloneUnitAndSwapMethodsIfApplies(unit, method, copy);
    	}
    	
    	return copy;
    }
    
    private static void cloneUnitAndSwapMethodsIfApplies(final Unit unit, final SootMethod originalMethod, final SootMethod copyMethod) {
    	final Unit copyUnit = unit;

    	if (copyUnit instanceof JAssignStmt) {
    		final JAssignStmt assign = (JAssignStmt)copyUnit;
    		if (assign.getRightOp() instanceof InvokeExpr) {
    			swapMethods(assign.getInvokeExpr(), originalMethod, copyMethod);
    		}
    	}
    	else if (copyUnit instanceof JInvokeStmt) {
    		final InvokeStmt invoke = (JInvokeStmt)copyUnit;
    		swapMethods(invoke.getInvokeExpr(), originalMethod, copyMethod);
    	}
    }
    
    private static void swapMethods(final InvokeExpr invokeExpr, final SootMethod fromMethod, final SootMethod toMethod) {
    	if (invokeExpr != null && invokeExpr.getMethod().equals(fromMethod)) {
    		invokeExpr.setMethodRef(toMethod.makeRef());
    	}
    }
    
    private static void addCallsToInstrumentingMethod(final SootMethod method, final Body body, final Unit cursor, final SootMethod copyMethod, final Local startTimeLocal, final Local mapLocal, final Unit sendAndSerializeStmt) {
    	InvokeExpr invokeExpr = null;
    	if ((copyMethod.getModifiers() & Modifier.STATIC) > 0) {
    		invokeExpr = Jimple.v().newStaticInvokeExpr(copyMethod.makeRef(), body.getParameterLocals());
    	}
    	else {
    		invokeExpr = Jimple.v().newVirtualInvokeExpr(body.getThisLocal(), copyMethod.makeRef(), body.getParameterLocals());
    	}
    	
    	final Unit lastStmt = body.getUnits().getPredOf(body.getUnits().getLast());
    	
    	Unit assignOrInvoke = null;
    	Unit retStmt = null;
    	if (!(copyMethod.getReturnType() instanceof VoidType)) {
    		final Local ret = Jimple.v().newLocal("$copyMethodReturnLocal", copyMethod.getReturnType());
    		body.getLocals().add(ret);
    		
    		assignOrInvoke = Jimple.v().newAssignStmt(ret, invokeExpr);
    		retStmt = Jimple.v().newReturnStmt(ret);
    	}
    	else {
    		assignOrInvoke = Jimple.v().newInvokeStmt(invokeExpr);
    		retStmt = Jimple.v().newReturnVoidStmt();
    	}
    	
    	final SootMethod setShouldRunRTTMethod = Scene.v().getMethod("<br.com.lealdn.offload.OffloadingManager: void setShouldRunRTT(boolean)>");
    	
    	body.getUnits().add(Jimple.v().newInvokeStmt(
    		Jimple.v().newStaticInvokeExpr(setShouldRunRTTMethod.makeRef(), IntConstant.v(0))
    	));
    	
    	final Local rxTxCountLocal = Jimple.v().newLocal("rxTxCount", soot.ArrayType.v(LongType.v(), 1));
    	body.getLocals().add(rxTxCountLocal);
    	
    	body.getUnits().add(
    		Jimple.v().newAssignStmt(rxTxCountLocal,
    			Jimple.v().newStaticInvokeExpr(Scene.v().getMethod("<br.com.lealdn.offload.Intercept: long[] getRxTxCount()>").makeRef())
    		)
        );
    	
    	body.getUnits().add(assignOrInvoke);

    	body.getUnits().add(Jimple.v().newInvokeStmt(
    		Jimple.v().newStaticInvokeExpr(setShouldRunRTTMethod.makeRef(), IntConstant.v(1))
    	));
    	
    	final SootMethod instrumentingMethod = Scene.v().getMethod("<br.com.lealdn.offload.Intercept: void updateMethodRuntime(java.lang.String,long,java.util.Map,long[])>");
        final List<Value> args = new ArrayList<>();
        args.add(StringConstant.v(method.getSignature()));
        args.add(startTimeLocal);
        args.add(mapLocal);
        args.add(rxTxCountLocal);

        final Unit invokeInstrument = Jimple.v().newInvokeStmt(
        	Jimple.v().newStaticInvokeExpr(instrumentingMethod.makeRef(), args)
        );

        body.getUnits().add(invokeInstrument);
        body.getUnits().add(retStmt);

        body.getTraps().add(Jimple.v().newTrap(Scene.v().loadClassAndSupport("java.lang.Throwable"), sendAndSerializeStmt, lastStmt, lastStmt));
    }
    
    private static Local createStartTimeLocal(final Body body) {
    	final Local startTimeLocal = Jimple.v().newLocal("startTimeLocal", LongType.v());
    	body.getLocals().add(startTimeLocal);
    	
    	return startTimeLocal;
    }

    public static void turnMethodPublic(final SootMethod method) {
        method.getDeclaringClass().setApplicationClass();
        method.setModifiers(method.getModifiers() & ~Modifier.PRIVATE);
    }
    
    public static Unit addThisRefToMap(final Local mapLocal, final Body body, final Unit cursor) {
        final InvokeStmt invStmt = Jimple.v().newInvokeStmt(
            Jimple.v().newVirtualInvokeExpr(mapLocal, getMapPutMethod().makeRef(), new ArrayList<Value>() {{
                add(StringConstant.v("@this"));
                add(((JimpleBody)body).getThisLocal());
            }})
        );
        
        body.getUnits().insertAfter(invStmt, cursor);
        return invStmt;
    }

    public static Unit addArgsRefToMap(final Local mapLocal, final Body body, final SootMethod method, Unit cursor) {
        for (int i = 0; i < method.getParameterCount(); i++) {  
            final List<Value> arg = new ArrayList<>();
            arg.add(StringConstant.v("@arg"+i));
            arg.add(((JimpleBody)body).getParameterLocal(i));
            
            final InvokeStmt invStmt = Jimple.v().newInvokeStmt(
                Jimple.v().newVirtualInvokeExpr(mapLocal, getMapPutMethod().makeRef(), arg)
            );
            body.getUnits().insertAfter(invStmt, cursor);
            cursor = invStmt;
        }
        
        return cursor;
    }
    
    public static Unit invokeConditionToOffloadIfNecessary(final SootMethod method, final Local mapLocal, final Local startTimeLocal, final Body body, final Unit cursor) {
        final Local shouldOffload = Jimple.v().newLocal("localShouldOffload", BooleanType.v());
        body.getLocals().add(shouldOffload);

        final List<Value> args = new ArrayList<>();
        args.add(StringConstant.v(method.getSignature()));
        args.add(mapLocal);
        
        Scene.v().loadClassAndSupport("br.com.lealdn.offload.Intercept");
        final Unit assign = Jimple.v().newAssignStmt(shouldOffload, 
        	Jimple.v().newStaticInvokeExpr( Scene.v().getMethod("<br.com.lealdn.offload.Intercept: boolean shouldOffload(java.lang.String,java.util.Map)>").makeRef(), args)
        );
        
        body.getUnits().insertAfter(assign, cursor);

        final Unit sucOfAssign = body.getUnits().getSuccOf(assign);
        final Unit assignStartTimeLocal = Jimple.v().newAssignStmt(startTimeLocal, 
        	Jimple.v().newStaticInvokeExpr( Scene.v().getMethod("<java.lang.System: long currentTimeMillis()>").makeRef())
        );
        
        body.getUnits().insertBefore(assignStartTimeLocal, sucOfAssign);
        
        final Unit ifstmt = Jimple.v().newIfStmt(
        	Jimple.v().newEqExpr(shouldOffload, IntConstant.v(0)),
        	assignStartTimeLocal
        );

        body.getUnits().insertAfter(ifstmt, assign);
        
        return ifstmt;
    }
    
    private static Type boxPrimitiveType(Type type) {
    	if (type instanceof RefLikeType) {
    		return type;
    	}
    	
    	if (type instanceof IntType) {
    		return RefType.v("java.lang.Integer");
    	} else if (type instanceof FloatType) {
    		return RefType.v("java.lang.Float");
    	} else if (type instanceof DoubleType) {
    		return RefType.v("java.lang.Double");
    	} else if (type instanceof LongType) {
    		return RefType.v("java.lang.Long");
    	} else if (type instanceof CharType) {
    		return RefType.v("java.lang.Character");
    	} else if (type instanceof ByteType) {
    		return RefType.v("java.lang.Byte");
    	} else if (type instanceof ShortType) {
    		return RefType.v("java.lang.Short");
    	} else if (type instanceof BooleanType) {
    		return RefType.v("java.lang.Boolean");
    	}
    	
    	return null;
    }
    
    private static SootMethod getPrimitiveMethodForBoxedLocal(final RefType type) {
    	switch (type.getClassName()) {
		    case "java.lang.Integer":
		    	return Scene.v().getMethod("<java.lang.Integer: int intValue()>");
    	}
    	
    	return null;
    }
    
    private static Map<String, Object> autoboxPrimitiveIfNecessary(final SootMethod returnMethod, final Local sendAndSerializeLocal, final Body body, Unit cursor) {
	    final Map<String, Object> autoboxResult = new HashMap<String, Object>();
		final Type castedTypeFromReturn = boxPrimitiveType(returnMethod.getReturnType());
		final Local functionResult = Jimple.v().newLocal("functionResult", castedTypeFromReturn);

		body.getLocals().add(functionResult);

	    final AssignStmt castStmt = Jimple.v().newAssignStmt(
			    functionResult,
		    Jimple.v().newCastExpr(sendAndSerializeLocal, castedTypeFromReturn));

	    body.getUnits().insertAfter(castStmt, cursor);

    	if (returnMethod.getReturnType() instanceof RefLikeType) {
    		autoboxResult.put("returnRes", functionResult);
    		autoboxResult.put("cursor", castStmt);
    	}
    	else {
		    final Local returnPrimitive = Jimple.v().newLocal("returnPrimitive", returnMethod.getReturnType());
		    body.getLocals().add(returnPrimitive);
		    
			final AssignStmt assignStmt = Jimple.v().newAssignStmt(returnPrimitive,
			    Jimple.v().newVirtualInvokeExpr(functionResult, getPrimitiveMethodForBoxedLocal((RefType)functionResult.getType()).makeRef()));
			body.getUnits().insertAfter(assignStmt, castStmt);
			
		    autoboxResult.put("returnRes", returnPrimitive);
		    autoboxResult.put("cursor", assignStmt);
    	}

	    return autoboxResult;
    }

    public static Unit[] invokeInterceptorWithNeededLocals(final SootMethod method, final Local mapLocal, final Body body, Unit cursor) {
    	final boolean hasReturn = !(method.getReturnType() instanceof VoidType);

    	final SootMethod sendAndSerialize = Scene.v().getMethod("<br.com.lealdn.offload.Intercept: java.lang.Object sendAndSerialize(java.lang.String,java.util.Map)>");
	    final Local returnRes = Jimple.v().newLocal("returnFromIntercept", sendAndSerialize.getReturnType());
	    body.getLocals().add(returnRes);

        final List<Value> args = new ArrayList<>();
        args.add(StringConstant.v(method.getSignature()));
        args.add(mapLocal);

        final AssignStmt stmt = Jimple.v().newAssignStmt(
        	returnRes,
            Jimple.v().newStaticInvokeExpr(
                sendAndSerialize.makeRef(),
                args));

        body.getUnits().insertAfter(stmt, cursor);
        
        if (hasReturn) {
			final Map<String, Object> autoboxResult = SootUtils.autoboxPrimitiveIfNecessary(method, returnRes, body, stmt);
			final Local returnVariable = (Local)autoboxResult.get("returnRes");
			final Unit cursorSendAndSerialize = (Unit)autoboxResult.get("cursor");

            final ReturnStmt retStmt = Jimple.v().newReturnStmt(returnVariable);
            body.getUnits().insertAfter(retStmt,  cursorSendAndSerialize);
            return new Unit[] { retStmt, stmt };
        }
        else {
        	final Unit retStmt = Jimple.v().newReturnVoidStmt();
        	body.getUnits().insertAfter(retStmt, stmt);
        	
        	return new Unit[] { retStmt, stmt };
        }
    }
    
    public static Map<String, Object> addMapToBody(final Body body, Unit cursor) {
        Scene.v().loadClassAndSupport("java.util.HashMap");
        
        final SootMethod hashMapConstructor = Scene.v().getMethod("<java.util.HashMap: void <init>()>");
        
        final Local mapLocal = Jimple.v().newLocal("mapToSerialize", RefType.v("java.util.HashMap"));
        body.getLocals().add(mapLocal);
        final AssignStmt assignStmt = Jimple.v().newAssignStmt(mapLocal,
            Jimple.v().newNewExpr(RefType.v("java.util.HashMap")));
        body.getUnits().insertAfter(assignStmt, cursor);
        final InvokeStmt invokeStmt = Jimple.v().newInvokeStmt(
                Jimple.v().newSpecialInvokeExpr(mapLocal, hashMapConstructor.makeRef()));
        
        body.getUnits().insertAfter(invokeStmt, assignStmt);
        
        return new HashMap<String, Object>() {{
            put("mapLocal", mapLocal);
            put("cursor", invokeStmt);
        }};
    }
    
    public static SootMethod getMapPutMethod() {
        return Scene.v().getMethod("<java.util.HashMap: java.lang.Object put(java.lang.Object,java.lang.Object)>");
    }
    
    public static Unit addLocalForFieldAndAddToMap(final SootField field, final Body body, Local mapLocal, Unit cursor) {
        final Local local = Jimple.v().newLocal("local" + String.valueOf(field.getSignature().hashCode()) + System.currentTimeMillis(), field.getType());
        
        body.getLocals().add(local);
        final AssignStmt staticFieldRef = Jimple.v().newAssignStmt(local, Jimple.v().newStaticFieldRef(field.makeRef()));
        body.getUnits().insertAfter(staticFieldRef, cursor);
        final SootMethod putMethod = getMapPutMethod();
        final List<Value> putArgs = new ArrayList<Value>() {{
            add(StringConstant.v("field-" + field.getSignature() + "-" + local.getName()));
            add(local);
        }};

        final InvokeStmt putInMap = Jimple.v().newInvokeStmt(
            Jimple.v().newVirtualInvokeExpr(mapLocal, putMethod.makeRef(), putArgs));
        body.getUnits().insertAfter(putInMap, staticFieldRef);
        
        return putInMap;
    }
    
    public static void turnFieldsPublic(final List<SootField> fields) {
        for (final SootField field : fields) {
            field.getDeclaringClass().setApplicationClass();
            field.setModifiers(field.getModifiers() & ~Modifier.PRIVATE & ~Modifier.FINAL);
        }
    }
    
    public static StaticFieldRef checkForStaticFieldRef(final Value value) {
        if (value instanceof StaticFieldRef) {
            return (StaticFieldRef)value;
        }
        return null;
    }
    
    public static SootMethod checkForMethod(final Value value) {
        if (value instanceof JStaticInvokeExpr) {
            return ((JStaticInvokeExpr)value).getMethod();
        }
        else if (value instanceof JSpecialInvokeExpr) {
            return ((JSpecialInvokeExpr)value).getMethod();
        }
        else if (value instanceof JVirtualInvokeExpr) {
            return ((JVirtualInvokeExpr)value).getMethod(); 
        }
        return null;
    }
    
    public static List<SootField> getStaticFieldsFromMethod(final SootMethod method, Set<SootMethod> visited) {
        if (visited.contains(method) || method.isJavaLibraryMethod()) 
            return new ArrayList<>();
        visited.add(method);
        method.getDeclaringClass().setApplicationClass();
        final Body body = method.retrieveActiveBody();
        
        Unit u = null;
        final List<SootField> res = new ArrayList<>();
        
        for (final Iterator<Unit> i = body.getUnits().snapshotIterator();i.hasNext(); u = i.next()) {
            if (u instanceof JAssignStmt) {
                final JAssignStmt assignStmt = (JAssignStmt)u;
                final StaticFieldRef ref = checkForStaticFieldRef(assignStmt.getRightOp());
                if (ref != null) {
                    res.add(ref.getField());
                }
                else {
                    final SootMethod bfsMethod = checkForMethod(assignStmt.getRightOp());
                    if (bfsMethod != null) {
                        res.addAll(getStaticFieldsFromMethod(bfsMethod, visited));
                    }
                }
            }
            else if (u instanceof JInvokeStmt) {
                final JInvokeStmt invokeStmt = (JInvokeStmt)u;
                final SootMethod bfsMethod = checkForMethod(invokeStmt.getInvokeExpr());
                if (bfsMethod != null) {
                    res.addAll(getStaticFieldsFromMethod(bfsMethod, visited));
                }
            }
        }
        
        return res;
    }
    
    public static boolean isAnnotated(final SootMethod m) {
        for (final Tag tag : m.getTags()) {
            try {
                VisibilityAnnotationTag vtag = (VisibilityAnnotationTag)tag;
                AnnotationTag atag = vtag.getAnnotations().get(0);
                if (atag.getType().equals("Lbr/com/lealdn/offload/OffloadCandidate;")) {
                    return true;
                }
            } catch(Exception e) {}
        }
        
        return false;
    }
}
