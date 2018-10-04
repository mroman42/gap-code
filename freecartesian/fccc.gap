LoadPackage("CAP");;

# A free cartesian closed category over a set of objects
fccc := CreateCapCategory("Free Cartesian Closed Category over a set");
IsFcccObj := ObjectFilter(fccc);
IsFcccMorph := MorphismFilter(fccc);

########################################
## TYPES
########################################
# Declaration of multiple types as objects of the category.
DeclareRepresentation("IsAtomRep", IsFcccObj and IsAttributeStoringRep, []);
DeclareRepresentation("IsToptRep", IsFcccObj and IsAttributeStoringRep, []);
DeclareRepresentation("IsProdRep", IsFcccObj and IsAttributeStoringRep, []);
DeclareRepresentation("IsExpoRep", IsFcccObj and IsAttributeStoringRep, []);
DeclareCategory("IsAtom", IsAtomRep);
DeclareCategory("IsTopt", IsAtomRep);
DeclareCategory("IsProd", IsAtomRep);
DeclareCategory("IsExpo", IsAtomRep);

FcccObjFamily := NewFamily("FcccObjFamily", IsFcccObj);
FcccType := NewType(FcccObjFamily, IsFcccObj);
AtomType := NewType(FcccObjFamily, IsAtom);
ToptType := NewType(FcccObjFamily, IsTopt);
ProdType := NewType(FcccObjFamily, IsProd);
ExpoType := NewType(FcccObjFamily, IsExpo);


# Atomic types.
DeclareAttribute("Label", IsAtom);
Atom := function (label)
    local r;
    r := Objectify(AtomType, rec());
    SetLabel(r, label);
    AddObject(fccc, r);
    return r;
end;

# Unit type.
Topt := function ()
    local r;
    r := Objectify(ToptType, rec());
    AddObject(fccc, r);
    return r;
end;

# Product types.
DeclareAttribute("FirstComp", IsProd);
DeclareAttribute("SecondComp", IsProd);
Prod := function (A,B)
    local r;
    if not(IsFcccObj(A)) or not(IsFcccObj(B)) then
        Error("Arguments to Prod are not objects");
    fi;
    r := Objectify(ProdType, rec());
    SetFirstComp(r, A);
    SetSecondComp(r, B);
    AddObject(fccc, r);
    return r;
end;

# Exponential types
DeclareAttribute("BaseComp", IsExpo);
DeclareAttribute("ExpComp", IsExpo);
Expo := function (A,B)
    local r;
    if not(IsFcccObj(A)) or not(IsFcccObj(B)) then
        Error("Arguments to Expo are not objects");
    fi;
    r := Objectify(ExpoType, rec());
    SetBaseComp(r, A);
    SetExpComp(r, B);
    AddObject(fccc, r);
    return r;
end;    


InstallMethod(ViewString, "Show the type", [IsFcccObj], function (s)
                  local a, b;
                  if IsAtom(s) then return Label(s); fi;
                  if IsTopt(s) then return "⊤"; fi;
                  if IsProd(s) then
                      a := ViewString(FirstComp(s));
                      b := ViewString(SecondComp(s));
                      return Concatenation("(",a," × ",b,")");
                  fi;
                  if IsExpo(s) then
                      a := ViewString(BaseComp(s));
                      b := ViewString(ExpComp(s));
                      return Concatenation("(",a," → ",b,")");
                  fi;
                  Error("The object has no type");
              end);

typeEquality := function (a,b)
    if IsAtom(a) and IsAtom(b) and Label(a) = Label(b) then return true; fi;
    if IsTopt(a) and IsTopt(b) then return true; fi;
    if IsProd(a) and IsProd(b) 
       and typeEquality(FirstComp(a),FirstComp(b)) 
       and typeEquality(SecondComp(a),SecondComp(b)) then return true; fi;
    if IsExpo(a) and IsExpo(b)
       and typeEquality(BaseComp(a), BaseComp(b))
       and typeEquality(ExpComp(a), ExpComp(b)) then return true; fi;
    return false;
end;


########################################
## ELEMENTS
########################################
DeclareRepresentation("IsTermRep", IsAttributeStoringRep, []);
DeclareCategory("IsTerm", IsTermRep);

DeclareRepresentation("IsAstRep", IsTerm and IsAttributeStoringRep, []);
DeclareRepresentation("IsConstRep", IsTerm and IsAttributeStoringRep, []);
DeclareRepresentation("IsVarRep", IsTerm and IsAttributeStoringRep, []);
DeclareRepresentation("IsAbsRep", IsTerm and IsAttributeStoringRep, []);
DeclareRepresentation("IsAppRep", IsTerm and IsAttributeStoringRep, []);
DeclareRepresentation("IsPairRep", IsTerm and IsAttributeStoringRep, []);
DeclareRepresentation("IsFstRep", IsTerm and IsAttributeStoringRep, []);
DeclareRepresentation("IsSndRep", IsTerm and IsAttributeStoringRep, []);

DeclareCategory("IsAst", IsAstRep);
DeclareCategory("IsConst", IsConstRep);
DeclareCategory("IsVar", IsVarRep);
DeclareCategory("IsAbs", IsAbsRep);
DeclareCategory("IsApp", IsAppRep);
DeclareCategory("IsPair", IsPairRep);
DeclareCategory("IsFst", IsFstRep);
DeclareCategory("IsSnd", IsSndRep);

TermFamily := NewFamily("TermFamily", IsTerm);
AstType := NewType(TermFamily, IsAst);
ConstType := NewType(TermFamily, IsConst);
VarType := NewType(TermFamily, IsVar);
AbsType := NewType(TermFamily, IsAbs);
AppType := NewType(TermFamily, IsApp);
PairType := NewType(TermFamily, IsPair);
FstType := NewType(TermFamily, IsFst);
SndType := NewType(TermFamily, IsSnd);


# Attributes for lambda calculus terms.

# Ast of the terminal type
Ast := function ()
    local r;
    r := Objectify(AstType, rec());
    return r;
end;

# Const(type, label)
DeclareAttribute("TypeOfExpr", IsConst);
DeclareAttribute("Label", IsConst);
Const := function (type, label)
    local r;
    r := Objectify(ConstType, rec());
    SetTypeOfExpr(r, type);
    SetLabel(r, label);
    return r;
end;

# Var(index)
DeclareAttribute("Index", IsVar);
Var := function (index)
    local r;
    r := Objectify(VarType, rec());
    SetIndex(r, index);
    return r;
end;

# Abs(type, exp)
DeclareAttribute("TypeOfExpr", IsAbs);
DeclareAttribute("Expr", IsAbs);
Abs := function (type, expr)
    local r;
    r := Objectify(AbsType, rec());
    SetTypeOfExpr(r, type);
    SetExpr(r, expr);
    return r;
end;

# App(fun, arg)
DeclareAttribute("Fun", IsApp);
DeclareAttribute("Arg", IsApp);
App := function (fun, arg)
    local r;
    r := Objectify(AppType, rec());
    SetFun(r, fun);
    SetArg(r, arg);
    return r;
end;

# Pair(first, second)
DeclareAttribute("Frst", IsPair);
DeclareAttribute("Second", IsPair);
Pair := function (first, second)
    local r;
    r := Objectify(PairType, rec());
    SetFrst(r, first);
    SetSecond(r, second);
    return r;
end;

# Fst(exp)
DeclareAttribute("Expr", IsFst);
Fst := function (expr)
    local r;
    r := Objectify(FstType, rec());
    SetExpr(r, expr);
    return r;
end;

# Snd(exp)
DeclareAttribute("Expr", IsSnd);
Snd := function (expr)
    local r;
    r := Objectify(SndType, rec());
    SetExpr(r, expr);
    return r;
end;


# Print lambda expression
PrintExpression := function (s)
    local a, b;

    if IsAst(s) then return "*"; fi;
    if IsConst(s) then return Label(s); fi;
    if IsVar(s) then return String(Index(s)); fi;
    if IsAbs(s) then
        a := PrintExpression(Expr(s));
        return Concatenation("λ(", a,")");
    fi;
    if IsApp(s) then
        a := PrintExpression(Fun(s));
        b := PrintExpression(Arg(s));
        return Concatenation(a," ",b);
    fi;
    if IsPair(s) then
        a := PrintExpression(Frst(s));
        b := PrintExpression(Second(s));
        return Concatenation("<",a,",",b,">");
    fi;
    if IsFst(s) then return Concatenation("(π₁ ",PrintExpression(Expr(s)),")"); fi;
    if IsSnd(s) then return Concatenation("(π₂ ",PrintExpression(Expr(s)),")"); fi;    
end;


# Compute the type of an expression
GetTypeOf := function (ctx , s)
    local newctx, v, w;
    
    if not IsTerm(s) then Error("when getting type. It is not a term"); fi;
    
    if IsAst(s) then return Topt(); fi;
    if IsConst(s) then return TypeOfExpr(s); fi;
    if IsVar(s) then 
        if Index(s) < 1 or Index(s) > Length(ctx) then 
            Error("Var out of bounds. Index: ", Index(s), " expression: ", PrintExpression(s), " where context is: ", ctx);
        fi;
        return ctx[Index(s)];
    fi;
    if IsAbs(s) then 
        newctx := StructuralCopy(ctx);
        Add(newctx, TypeOfExpr(s), 1);
        return Expo(TypeOfExpr(s) , GetTypeOf(newctx, Expr(s)));
    fi;
    if IsApp(s) then
        v := GetTypeOf(ctx, Fun(s));
        w := GetTypeOf(ctx, Arg(s));
        if not IsExpo(v) then 
            Error("Non-typeable", ViewString(s), ", because ", ViewString(v), " is not an exponential"); fi;
        if not typeEquality(BaseComp(v), w) then 
            Error("Non-typeable ", PrintExpression(s), " because arg of ", ViewString(v), " is not ", ViewString(w)); fi;
        return ExpComp(v);
    fi;
    if IsPair(s) then return Prod(GetTypeOf(ctx, Frst(s)), GetTypeOf(ctx, Second(s))); fi;
    if IsFst(s) then
        if not IsProd(GetTypeOf(ctx, Expr(s))) then 
            Error("ill-typed expression: ",ViewString(Expr(s))); 
        fi;
        return FirstComp(GetTypeOf(ctx, Expr(s))); 
    fi;
    if IsSnd(s) then return SecondComp(GetTypeOf(ctx, Expr(s))); fi;
    
    Error("Pattern-matching error");
end;
    
# Print lambda terms in DeBruijn notation.
InstallMethod(ViewString, "Show the term", [IsTerm], function(s)
                  
                  #return PrintExpression(s);
                  return Concatenation(PrintExpression(s) ," : ",ViewString(GetTypeOf([],s)));
                  
              end);

########################################
## Simplification
########################################
termEquality := function (a,b)
    if IsAst(a) and IsAst(b) then return true; fi;
    if IsConst(a) and IsConst(b) then return true; fi;
    if IsVar(a) and IsVar(b) then return Index(a) = Index(b); fi;
    if IsAbs(a) and IsAbs(b) 
       and typeEquality(TypeOfExpr(a),TypeOfExpr(b))
       and termEquality(Expr(a),Expr(b)) then return true; fi;
    if IsApp(a) and IsApp(b) and termEquality(Fun(a),Fun(b)) and termEquality(Arg(a),Arg(b)) then return true; fi;
    if IsPair(a) and IsPair(b) 
       and termEquality(Frst(a),Frst(b)) 
       and termEquality(Second(a),Second(b)) then return true; fi;
    if IsFst(a) and IsFst(b) and termEquality(Expr(a),Expr(b)) then return true; fi;
    if IsSnd(a) and IsSnd(b) and termEquality(Expr(a),Expr(b)) then return true; fi;
    return false;
end;

incrFreeVar := function (n, a)
    if IsAst(a) then return a; fi;
    if IsConst(a) then return a; fi;
    if IsVar(a) then
        if Index(a) > n then 
            return Var(Index(a) + 1);
        else
            return a;
        fi;
    fi;
    if IsAbs(a) then
        return Abs(TypeOfExpr(a), incrFreeVar(n+1, Expr(a)));
    fi;
    if IsApp(a) then
        return App(incrFreeVar(n, Fun(a)), incrFreeVar(n, Arg(a)));
    fi;
    if IsPair(a) then
        return Pair(incrFreeVar(n, Frst(a)), incrFreeVar(n, Second(a)));
    fi;
    if IsFst(a) then return Fst(incrFreeVar(n,Expr(a))); fi;
    if IsSnd(a) then return Snd(incrFreeVar(n,Expr(a))); fi;
end;


substitute := function (n , x , m)
    if IsAst(m) then return m; fi;
    if IsConst(m) then return m; fi;
    if IsVar(m) then 
        if Index(m) = n then 
            return x; 
        else 
            if Index(m) > n then 
                return Var(Index(m)-1);
            else 
                return m; 
            fi;
        fi; 
    fi;
    if IsAbs(m) then return Abs(TypeOfExpr(m), substitute(n+1, incrFreeVar(0,x), Expr(m))); fi;
    if IsApp(m) then return App(substitute(n,x,Fun(m)), substitute(n,x,Arg(m))); fi;
    if IsPair(m) then return Pair(substitute(n,x,Frst(m)), substitute(n,x,Second(m))); fi;
    if IsFst(m) then return Fst(substitute(n,x,Expr(m))); fi;
    if IsSnd(m) then return Snd(substitute(n,x,Expr(m))); fi;
end;


unitRule := function (ctx , a)
    # Eta reduction for the unit type.
    #  a > unit
    if typeEquality(GetTypeOf(ctx , a), Topt()) then return Ast(); fi;
    return a;
end;

tounitRule := function (ctx, a)
    local typeofa;
    typeofa := GetTypeOf(ctx, a);
    
    if IsConst(a) then
        if IsExpo(typeofa) then
            if typeEquality(ExpComp(typeofa), Topt()) then
                return Abs(BaseComp(typeofa), Ast());
            fi;
        fi;
    fi;
    
    return a;
end;

fstRule := function (a)
    # Fst beta reduction
    if IsFst(a) and IsPair(Expr(a)) then
        return Frst(Expr(a));
    else
        return a;
    fi;
end;

sndRule := function (a)
    # Snd beta reduction
    if IsSnd(a) and IsPair(Expr(a)) then
        return Second(Expr(a));
    else
        return a;
    fi;
end;

pairRule := function (a)
    # Pair eta reduction
    #   pair (fst a) (snd a) > a
    if IsPair(a) and IsFst(Frst(a)) and IsSnd(Second(a))
       and termEquality(Expr(Frst(a)), Expr(Second(a))) then
        return Expr(Frst(a));
    else
        return a;
    fi;
end;

etaRule := function (ctx,a)
    # Eta extensionality for functions
    #   lambda (app f 1) > f
    # (var 1) must not appear in f
    
    local varnfree, decrease, initialtype, finaltype, r;
    varnfree := function (n,f) Error("not yet implemented"); end;
    varnfree := function (n,f)
        if IsAst(f) then return true; fi;
        if IsConst(f) then return true; fi;
        if IsVar(f) then return not Index(f) = n; fi;
        if IsAbs(f) then return varnfree(n+1,f); fi;
        if IsApp(f) then return varnfree(n,Fun(f)) and varnfree(n,Arg(f)); fi;
        if IsPair(f) then return varnfree(n,Frst(f)) and varnfree(n,Second(f)); fi;
        if IsFst(f) then return varnfree(n,Expr(f)); fi;
        if IsSnd(f) then return varnfree(n,Expr(f)); fi;
    end;
    
    # After substitution, variables must decrease a number
    decrease := function (n,f) Error("not yet implemented"); end;
    decrease := function (n,f)
        if IsAst(f) then return f; fi;
        if IsConst(f) then return f; fi;
        if IsVar(f) and Index(f) > n then return Var(Index(f)-1); fi;
        if IsAbs(f) then return Abs(TypeOfExpr(f), decrease(n+1,Expr(f))); fi;
        if IsApp(f) then return App(decrease(n,Fun(f)), decrease(n,Arg(f))); fi;
        if IsPair(f) then return Pair(decrease(n,Frst(f)), decrease(n,Second(f))); fi;
        if IsFst(f) then return Fst(decrease(n,Expr(f))); fi;
        if IsSnd(f) then return Snd(decrease(n,Expr(f))); fi;        
    end;
    
    
    initialtype := GetTypeOf(ctx,a);
        
    if IsAbs(a) and IsApp(Expr(a)) and IsVar(Arg(Expr(a))) and Index(Arg(Expr(a))) = 1 and varnfree(1,Fun(Expr(a))) then
        r := decrease(1,Fun(Expr(a)));
        finaltype := GetTypeOf(ctx,r);
        if not typeEquality(initialtype,finaltype) then 
            Error("Subject reduction failed.\n", "Initial term: ", PrintExpression(a), "\nFinal term: ", PrintExpression(r));
        fi;
        return r;
    else
        return a;
    fi;    
end;

appRule := function (a)
    # Beta reduction
    #  (λ phi[1]) a > phi[a]
    if IsApp(a) and IsAbs(Fun(a)) then
        return substitute(1, Arg(a), Expr(Fun(a)));
    else
        return a;
    fi;
end;

simplify := function (ctx,a, debug) 
    Error("not yet implemented!");
    return a;
end;

                
recursivelySimplify := function (ctx , a)
    local newctx;
    
    if IsAst(a) then return a; fi;
    if IsConst(a) then return a; fi;
    if IsVar(a) then return a; fi;
    if IsAbs(a) then 
        newctx := StructuralCopy(ctx);
        Add(newctx, TypeOfExpr(a), 1);
        return Abs(TypeOfExpr(a), simplify(newctx, Expr(a), false));
    fi;
    if IsApp(a) then return App(simplify(ctx,Fun(a),false), simplify(ctx,Arg(a),false)); fi;
    if IsPair(a) then return Pair(simplify(ctx,Frst(a),false), simplify(ctx,Second(a),false)); fi;
    if IsFst(a) then return Fst(simplify(ctx,Expr(a),false)); fi;
    if IsSnd(a) then return Snd(simplify(ctx,Expr(a),false)); fi;
end;


simplify := function (ctx , a, debug)
    local newa;
    if debug then
        Print(Concatenation(["simpl: ", PrintExpression(a), "\n"]));
    fi;
    newa := recursivelySimplify(ctx,etaRule(ctx,appRule(pairRule(sndRule(fstRule(unitRule(ctx,tounitRule(ctx,a))))))));
    if debug then
        Print(Concatenation(["simpl: ", PrintExpression(newa), "\n"]));
    fi;
    if termEquality(newa, a) then return a; else return simplify(ctx, newa, debug); fi;
end;



########################################
## Categorical structure
########################################
DeclareRepresentation("IsFcccMorphismRep", IsAttributeStoringRep, []);
DeclareCategory("IsFcccMorphism", IsFcccMorphismRep);
FcccMorphismType := NewType(NewFamily("FcccMorphismFamily"), IsFcccMorphism);

DeclareAttribute("Source", IsFcccMorphism);
DeclareAttribute("Target", IsFcccMorphism);
DeclareAttribute("Term", IsFcccMorphism);

AsFCCCMorphism := function (term)
    local type, r;
    
    if not IsTerm(term) then Error("Is not a term"); fi;
    type := GetTypeOf([], term);
    if not IsExpo(type) then Error("It is not an arrow"); fi;
    
    r := Objectify(FcccMorphismType, rec());
    SetSource(r, BaseComp(type));
    SetRange(r, ExpComp(type));
    SetTerm(r, simplify([], term,false));
    AddMorphism(fccc, r);
    
    return r;
end;

CreateFreeMorphismBetween := function (A,B,label)
    local r;
    
    r := Objectify(FcccMorphismType, rec());
    SetSource(r, A);
    SetRange(r, B);
    SetTerm(r, simplify([], Const(Expo(A,B), label), false));
    AddMorphism(fccc, r);
    return r;
end;




AddIsEqualForObjects(fccc, function(A,B) return typeEquality(A,B); end);
AddIsEqualForMorphisms(fccc, function(f,g) return termEquality(Term(f),Term(g)); end);
AddIsCongruentForMorphisms(fccc, function(f,g) return termEquality(Term(f),Term(g)); end);


AddIdentityMorphism(fccc, function(A)
                       return AsFCCCMorphism( Abs(A, Var(1)) );
                   end);

AddPreCompose(fccc, function(f, g)
                 local ft, gt, fA, fB, gB, gC;
                 
                 ft := Term(f);
                 gt := Term(g);
                
                 return AsFCCCMorphism( Abs(Source(f), App(gt,App(ft,Var(1)))) );
             end);

AddTerminalObject(fccc, function() return Topt(); end);
                  
AddUniversalMorphismIntoTerminalObject(fccc, function (A)
                                          return AsFCCCMorphism( Abs(A , Ast()) );
                                      end);


AddTensorProductOnObjects(fccc, function (a,b)
                             return Prod(a,b);
                         end);

AddDirectProduct(fccc, function (D)
                    local r, d;
                    r := D[Length(D)];
                    Remove(D);
                    
                    for d in Reversed(D) do
                        r := Prod(d,r);
                    od;
                    
                    return r;
                end);

AddProjectionInFactorOfDirectProduct(fccc, function(D,k)
                                        local n, arg;
                                        
                                        n := Length(D);
                                        arg := Var(1);
                                        
                                        while true do
                                            if k = 1 then arg := Fst(arg); break; fi;
                                            if k = 2 and n = 2 then arg := Snd(arg); break; fi;
                                            
                                            k := k-1;
                                            n := n-1;
                                            arg := Snd(arg);
                                        od;
                                            
                                        return AsFCCCMorphism( Abs(DirectProduct(D), arg) );
                                    end);

AddUniversalMorphismIntoDirectProduct(fccc, function (D,tau)
                                         local s, morphs, r, t;
                                         
                                         s := Source(tau[1]);
                                         morphs := Reversed(List(tau,Term));
                                         Remove(morphs,1);
                                         
                                         r := App(Term(tau[Length(tau)]),Var(1));
                                         for t in morphs do
                                             r := Pair(App(t, Var(1)), r);
                                         od;
                                         
                                         return AsFCCCMorphism(Abs(s, r));
                                     end);

AddInternalHomOnObjects(fccc, function(a,b) return Expo(a,b); end);

AddEvaluationMorphismWithGivenSource(fccc, function(a,b,s)
                                        
                                        return AsFCCCMorphism( 
                                                       Abs( Prod(InternalHomOnObjects(a,b), a),
                                                            App(Fst(Var(1)), Snd(Var(1)))
                                                          ) 
                                                   );
                                        
                                    end);

AddCoevaluationMorphismWithGivenRange(fccc, function(a,b,r)
                                         
                                         return AsFCCCMorphism(
                                                                Abs( a, Abs( b, Pair(Var(2),Var(1))))
                                                    );
                                         
                                     end);

AddLambdaIntroduction(fccc, function (alpha)
                         
                         return AsFCCCMorphism( Abs(TerminalObject(fccc) , Term(alpha)) );
                         
                     end);


AddLambdaElimination(fccc, function (a, b, f)
                        
                        return AsFCCCMorphism( App(Term(f), Ast()) );
                        
                    end);


AddTensorProductToInternalHomAdjunctionMap(fccc, function (a, b, f)
                                              
                                              return AsFCCCMorphism( Abs(a, Abs(b, App(Term(f), Pair(Var(2),Var(1))))) );
                                                  
                                          end);
