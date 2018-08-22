LoadPackage("CAP");

finset := CreateCapCategory("FinSet");

IsFinSetObj := ObjectFilter(finset);
IsFinSetMorph := MorphismFilter(finset);

# Finite Sets
DeclareRepresentation("IsFinSetRep", IsAttributeStoringRep, []);
DeclareCategory("IsFinSet", IsFinSetRep);
FinSetType := NewType(NewFamily("FinSetFamily"), 
                      IsFinSet and IsFinSetObj and IsCapCategoryObject and IsFinite);

DeclareAttribute("UnderlyingList", IsFinSet);
DeclareAttribute("Size", IsFinSet);


FinSet := function(list)
    local r;

    if not(IsList(list) and IsFinite(list)) then
        Error("Argument must be a list");
    fi;

    r := Objectify(FinSetType, rec());
    SetUnderlyingList(r, StructuralCopy(list));
    AddObject(finset, r);
    
    return r;
end;

InstallMethod(Size, "Size of the finite set", [IsFinSet],
              function(fset)
                  return Size(UnderlyingList(fset));
              end);

#! @Description
#! Equality between finite sets.
InstallMethod(\=, "FinSet equality", [IsFinSet, IsFinSet],
              function (A,B)
                  local r, x;
                  
                  r := true;                  
                  if not(Size(A) = Size(B)) then
                      r := false;
                  fi;
                  for x in UnderlyingList(A) do
                      if not(x in UnderlyingList(B)) then
                          r := false;
                          break;
                      fi;
                  od;         
                  
                  return r;
              end);

InstallMethod(ViewString, "Show a finite set", [IsFinSet],
              function(s)
                  return String(UnderlyingList(s));
              end);


# Morphisms between finite sets
DeclareRepresentation("IsFinSetMorphismRep", IsAttributeStoringRep, []);
DeclareCategory("IsFinSetMorphism", IsFinSetMorphismRep);
FinSetMorphismType := NewType(NewFamily("FinSetMorphismFamily"), IsFinSetMorphism and IsCapCategoryMorphism);

DeclareAttribute("Source", IsFinSetMorphism);
DeclareAttribute("Range", IsFinSetMorphism);
DeclareAttribute("Arrow", IsFinSetMorphism);


FinSetMorphism := function (source, target, arrow)
    local r, n, x, pair, b;
    
    # Checks types
    if not(IsFinSet(source)) then Error("Type error: source is not a FinSet"); fi;
    if not(IsFinSet(target)) then Error("Type error: target is not a FinSet"); fi;
    if not(IsList(arrow)) then Error("Type error: arrow is not a List"); fi;
    
    
    # Checks well-definedness
    if not(Size(source) = Size(arrow)) then
        Print("Size of source: ");
        Print(Size(source));
        Print("\n");        
        Print("Size of arrow: ");
        Print(Size(arrow));
        Error("Arrow is not well-defined, incorrect size");
    fi;
    
    for x in UnderlyingList(source) do
        b := false;
        for pair in arrow do
            if pair[1] = x then 
                b := true;
                break;
            fi;
        od;
        if b = false then
            Error("Arrow is only partially defined");
        fi;
    od;    
            
    for pair in arrow do
        if not(IsList(pair)) then Error("Type error: arrow is not composed of pairs"); fi;
        if not(Size(pair) = 2) then Error("Arrow is not composed of pairs"); fi;
        if not(pair[1] in UnderlyingList(source)) then Error("Type error: preimage is not in source"); fi;
        if not(pair[2] in UnderlyingList(target)) then Error("Type error: image is not in range"); fi;
    od;
    
    # Creates the morphism
    r := Objectify(FinSetMorphismType, rec());
    SetSource(r,source);
    SetRange(r,target);
    SetArrow(r,arrow);
    AddMorphism(finset,r);
    
    return r;
end;

InstallMethod(ViewString, "Show a finite set morphism", [IsFinSetMorphism],
              function(m)
                  local s, x;
                  s := "";
                  
                  for x in Arrow(m) do
                      s := Concatenation(s, String(x[1]), " ↦ ", String(x[2]), ",    ");
                  od;
                        
                  return Concatenation("Morphism from:   ",
                                       ViewString(Source(m)) , 
                                       "    to:   ", 
                                       ViewString(Range(m)), 
                                       "    given by:     " , 
                                       s);
              end);

Evaluate := function (f,a)
    local x;
    
    if not(IsFinSetMorphism(f)) then
        Error("Type error: it is not a morphism between FinSet");
    fi;

    for x in Arrow(f) do
        if (a = x[1]) then 
            return x[2]; 
        fi;
    od;
    
    Error("Type error: it is not an element of the source");
end;

####################
# CAP Category
####################
AddPreCompose(finset, 
             function (f, g)
                 local mph, r, fp, gp;
                 r := [];
    
                 if not(Source(g) = Range(f)) then 
                     Error("Non-composable morphisms");
                 fi;
                 
                 for fp in Arrow(f) do
                     for gp in Arrow(g) do
                         if (fp[2] = gp[1]) then
                             Add(r,[fp[1],gp[2]]);
                         fi;
                     od;
                 od;
                 
                 mph := FinSetMorphism(Source(f),Range(g),r);
                 return mph;
             end);

AddIdentityMorphism(finset, 
                   function (A)
                       local l, r;
                       l := List(UnderlyingList(A), x -> [x,x]);
                       r := FinSetMorphism(A,A,l);
                       return r;
                   end);

AddIsEqualForObjects(finset, function (A,B) return A = B; end);

AddTerminalObject(finset, 
                 function ()
                     return FinSet(['*']);
                 end);

AddUniversalMorphismIntoTerminalObject(finset, 
                                      function(A) 
                                          local l, r;
                                          l := List(UnderlyingList(A), x -> [x,'*']);
                                          r := FinSetMorphism(A,TerminalObject(finset),l);
                                          return r;
                                      end);
AddInitialObject(finset,
                function ()
                    return FinSet([]);
                end);

AddUniversalMorphismFromInitialObject(finset,
                                     function(A)
                                         local l, r;
                                         l := [];
                                         r := FinSetMorphism(InitialObject(finset), A, l);
                                         return r;
                                     end);

AddTensorProductOnObjects(finset,
                         function(A,B)
                             local l, r;
                             l := Cartesian(UnderlyingList(A), UnderlyingList(B));
                             r := FinSet(l);
                             return r;
                         end);

AddDirectProduct(finset, 
                function(D)
                    local l,r;
                    l := Cartesian(List(D, UnderlyingList));
                    r := FinSet(l);
                    return r;
                end);

AddUniversalMorphismIntoDirectProduct(finset,
                                     function(D,tau)
                                         local A, m, a;
                                         A := Source(tau[1]);
                                         
                                         m := List(UnderlyingList(A), a -> [a, List(tau, t -> Evaluate(t,a))]);
                                         
                                         return FinSetMorphism(Source(tau[1]),DirectProduct(D),m);
                                     end);

AddProjectionInFactorOfDirectProduct(finset,
                                    function(P,k)
                                        local D, m;
                                        
                                        D := DirectProduct(P);
                                        m := List(UnderlyingList(D), d -> [d,d[k]]);
                                        
                                        return FinSetMorphism(D,P[k],m);
                                    end);

                                    

backtrack := function(A,B,l,i)
    local r, n, b;
    r := [];
    
    if i > Size(A) then 
        return [l];
    fi;
    
    for b in B do
        n := StructuralCopy(l);
        Add(n,[A[i],b]);
        Append(r,backtrack(A,B,n,i+1));
    od;
    
    return r;
end;

AddInternalHomOnObjects(finset,
                       function(A,B)
                           return FinSet(List(backtrack(UnderlyingList(A),UnderlyingList(B),[],1), 
                                              m -> FinSetMorphism(A,B,m)));
                       end);

AddIsCongruentForMorphisms(finset,
                          function(f,g)
                              local r, p, q;
                              
                              if not(Source(f) = Source(g)) or not(Range(f) = Range(g)) then
                                  return false;
                              fi;
                              for p in Arrow(f) do
                                  for q in Arrow(g) do
                                      if (p[1] = q[1]) and not(p[2] = q[2]) then
                                          return false;
                                      fi;
                                  od;
                              od;
                                  
                              return true;
                          end);


AddEvaluationMorphismWithGivenSource(finset,
                                    function (A,B,S)
                                        local m, a, s;
                                        m := [];
                                        
                                        for s in UnderlyingList(S) do
                                            for a in Arrow(s[1]) do
                                                if a[1] = s[2] then
                                                    Add(m,[s, a[2]]);
                                                fi;
                                            od;
                                        od;
                                        
                                        return FinSetMorphism(S,B,m);
                                    end);

AddCoevaluationMorphismWithGivenRange(finset,
                                     function(A,B,R)
                                         local m;
                                         
                                         m := List(UnderlyingList(A), 
                                                   a -> [a, 
                                                         FinSetMorphism(B,
                                                                        DirectProduct(A,B),
                                                                        List(UnderlyingList(B),
                                                                             b -> [b,[a,b]]
                                                                            )
                                                                       )
                                                        ]
                                                  );

                                         return FinSetMorphism(A,R,m);
                                     end);


AddTensorProductToInternalHomAdjunctionMap(finset,
                                          function(A,B,f)
                                              local m, n, x, a, b, C;
                                              C := Range(f);
                                              
                                              m := [];
                                              for a in UnderlyingList(A) do
                                                  n := [];
                                                  for x in Arrow(f) do
                                                      if a = x[1][1] then
                                                          Add(n,[x[1][2], x[2]]);
                                                      fi;
                                                  od;
                                                  Add(m, [a, FinSetMorphism(B,C,n)]);
                                              od;
    
                                              return FinSetMorphism(A,InternalHomOnObjects(B,C),m);
                                          end);

AddInternalHomToTensorProductAdjunctionMap(finset,
                                          function(B,C,g)
                                              local A, a, b, c, m;
                                              A := Source(g);
                                              m := [];
                                              
                                              for a in UnderlyingList(A) do
                                                  for b in UnderlyingList(B) do
                                                      c := Evaluate(Evaluate(g,a), b);
                                                      Add(m, [[a,b], c]);
                                                  od;
                                              od;
                                              
                                              return FinSetMorphism(DirectProduct(A,B), C, m);
                                          end
                                          );
