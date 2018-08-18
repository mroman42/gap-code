LoadPackage("CAP");


# Finite Sets
DeclareRepresentation("IsFinSetRep", IsAttributeStoringRep, []);
DeclareCategory("IsFinSet", IsFinSetRep);
FinSetType := NewType(NewFamily("FinSetFamily"), IsFinSet);

DeclareAttribute("UnderlyingList", IsFinSet);
DeclareAttribute("Size", IsFinSet);


FinSet := function(list)
    local r;

    if not(IsList(list)) then
        Error("Argument must be a list");
    fi;

    r := Objectify(FinSetType, rec());
    SetUnderlyingList(r, StructuralCopy(list));

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
FinSetMorphismType := NewType(NewFamily("FinSetMorphismFamily"), IsFinSetMorphism);

DeclareAttribute("Source", IsFinSetMorphism);
DeclareAttribute("Range", IsFinSetMorphism);
DeclareAttribute("Arrow", IsFinSetMorphism);


FinSetMorphism := function (source, target, arrow)
    local r, n, x, pair, b;
    
    # Checks types
    if not(IsFinSet(source)) or not(IsFinSet(target)) or not(IsList(arrow)) then
        Error("Type error");
    fi;
    
    # Checks well-definedness
    if not(Size(source) = Size(arrow)) then
        Error("Arrow is not well-defined");
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
        if not(IsList(pair)) then Error("Type error"); fi;
        if not(Size(pair) = 2) then Error("Arrow is not composed of pairs"); fi;
        if not(pair[1] in UnderlyingList(source)) then Error("Type error"); fi;
        if not(pair[2] in UnderlyingList(target)) then Error("Type error"); fi;
    od;
    
    # Creates the morphism
    r := Objectify(FinSetMorphismType, rec());
    SetSource(r,source);
    SetRange(r,target);
    SetArrow(r,arrow);
    
    return r;
end;

Compose := function (g, f)
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
    
    mph := Objectify(FinSetMorphismType, rec());
    SetSource(mph,Source(f));
    SetRange(mph,Range(g));
    SetArrow(mph,r);
    return mph;
end;

InstallMethod(ViewString, "Show a finite set morphism", [IsFinSetMorphism],
              function(m)
                  return Concatenation("Morphism ", 
                                       ViewString(Source(m)) , 
                                       " -> ", 
                                       ViewString(Range(m)), 
                                       " given by: " , 
                                       String(Arrow(m)));
              end);

IdMorphism := function (A)
    local l, r;
    l := List(UnderlyingList(A), x -> [x,x]);
    
    r := Objectify(FinSetMorphismType, rec());
    SetSource(r,A);
    SetRange(r,A);
    SetArrow(r,l);
    return r;
end;



####################
# CAP Category
####################
finset := CreateCapCategory("FinSet");
AddPreCompose(finset, Compose);
AddIdentityMorphism(finset, IdMorphism);
AddIsEqualForObjects(finset, function (A,B) return A = B; end);
