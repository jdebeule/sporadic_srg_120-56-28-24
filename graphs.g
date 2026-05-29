###################
#                 #
#     SPREADS     #
#                 #
###################


# We construct the hyperbolic quadric Q+(7,2) using FinInG, and the associated group PGO+(8,2).

LoadPackage("fining");
quad := HyperbolicQuadric(7,2);;
pgo := CollineationGroup(quad);;

# Next, we select one system of generators.
# We construct the subgroup of pgo that stabilises the systems of generators.

sigma1 := Random(Solids(quad));;
system := Filtered(Solids(quad), sigma2 -> ProjectiveDimension(Meet(sigma1, sigma2)) in [0,2] );;
pgoAlt := FiningSetwiseStabiliser( pgo, system );;

# We use Grape to select an ovoid and a spread in Q+(7,2).
# Then we construct the collection of all spreads in our fixed system of generators.

gammaOv := Graph(pgo, List(Points(quad)), OnProjSubspaces, function(P,Q) if P*Q^PolarityOfProjectiveSpace(quad) then return false; else return true; fi; end);;
ov := List(CompleteSubgraphs(gammaOv,9)[1], i -> VertexName(gammaOv,i));;
gammaSpr := Graph(pgoAlt, system, OnProjSubspaces, function(U,V) if ProjectiveDimension(Meet(U,V)) = -1 then return true ; else return false; fi; end);;
spread := Set(CompleteSubgraphs(gammaSpr,9)[1], i -> VertexName(gammaSpr,i));;
spreadsOfSystem := Set(FiningOrbit( pgoAlt, spread, OnSetsProjSubspaces ));;

# We let G be the setwise stabiliser in pgoAlt of the ovoid ov and two designated points of the ovoid.

G := FiningSetwiseStabiliser( pgoAlt, ov );;
G := FiningSetwiseStabiliser( G, Set( ov{[ 1,2 ]} ) );;

# We select the orbit of G on the spreads in our chosen system of generators of size 120.

spreads := Filtered( FiningOrbits( G, spreadsOfSystem, OnSetsProjSubspaces ), orb -> Size(orb) = 120)[1];;

# We already know that G acts transitively on spreads.
# We check that it acts generously transitively.
# It suffices to fix one spread spr1 in spreads, look at its stabiliser Gstab in G, and check that in each orbit of Gstab,
# if we pick a random representative, there exists an element in G that swaps it with spr1.
# After running the code below, IsGenTrans is true if G acts generously transitively, and false otherwise.

spr1  := spreads[1];;
Gstab := FiningSetwiseStabiliser(G, spr1 );;
orbs := FiningOrbits( Gstab, Set(spreads), OnSetsProjSubspaces );;
IsGenTrans := true;;
GList := List(G);;
for orb in orbs do
  rep := orb[1];
  swap := false;
  i := 1;
  while ( (not swap) and (i <= Size(G)) ) do
    g := GList[i];
    if OnSetsProjSubspaces( spr1, g ) = rep and OnSetsProjSubspaces( rep, g ) = spr1 then
      swap := true;
    fi;
    i := i+1;
  od;
  if not swap then
    IsGenTrans := false;
  fi;
od;
IsGenTrans;
Size(orbs);

# The fact that IsGenTrans is true and that Size(orbs) equals 7 proves Proposition 3.2.

# Given a spread, every point of ov is in exactly one generator of the spread. This induces an ordering on the generators of the spread.
# The function spreadsort orders a spread accordingly.
# We order the spreads using the spreadsort function.

spreadsort := function(spr)
  local res, i, j;
  res := [];;
  for i in [1..9] do
    Add(res, Filtered(spr, sigma -> ov[i] * sigma)[1]);
  od;
  return res;
end;;

# Next, we check that the orbitals of G can be distinguished using the invariants listed in our paper.
# It suffices to check if we fix spr1, these invariants distinguish representatives of the orbits of Gstab.
# We introduce functions that return these invariants.
# When running the functions, one should make sure that the spreads were sorted using spreadsort.

inv1 := function(s, t)
  return ProjectiveDimension(Meet(s[1], t[2])) + ProjectiveDimension(Meet(s[2], t[1]));
end;;

inv2 := function(spr1, spr2)
  local i, j;
  return Size( Intersection( List( [1,2], i -> Filtered([3..9], j -> ProjectiveDimension(Meet(spr1[i], spr2[j])) = 1 ) ) ) );
end;;

spr1 := spreadsort(spr1);;
reps := List( orbs, orb -> spreadsort( orb[1] ) );;
List( reps, rep -> [ inv1( spr1, rep ), inv2( spr1, rep ), spr1 = rep ] );

# One sees that the invariants indeed distinguish the representatives of the Gstab orbits, and that they take
# the values as defined in the paper.
# We can now use them to construct our association scheme.
# The function relation takes a pair of sorted spreads, and returns the number of the relation that contains this pair.
# Assoc is a list of matrices, Assoc[k] is the adjacency matrix of the kth relation.

sortedspreads := List( spreads, s -> spreadsort( s ) );;

relation := function(spread1, spread2)
  local i1, i2, spr1, spr2;
  if spread1 = spread2 then
    return 0;
  else
    spr1 := spreadsort(spread1);
    spr2 := spreadsort(spread2);
    i2 := inv2(spr1, spr2);
    if i2 = 3 then
      return 6;
    elif i2 = 1 then
      return 5;
    else
      i1 := inv1(spr1,spr2);
      if i2 = 2 then
        if i1 = -2 then
          return 3;
        else
          return 4;
        fi;
      else
        if i1 = -2 then
          return 2;
        else
          return 1;
        fi;
      fi;
    fi;
  fi;
end;;

Assoc := List([1..6], i -> NullMat(120,120));;
for i in [1..120] do
  for j in [1..120] do
    k := relation(sortedspreads[i], sortedspreads[j]);
    if not k = 0 then
      Assoc[k][i,j] := 1;
    fi;
  od;
od;

# We construct the matrix of eigenvalues Pmat of the association scheme.
# Using the power of hindsight, we know that only relation 4 has a different eigenvalues on all eigenspaces of the scheme.
# Thus, the eigenspaces of relation 4 give us the different eigenspaces of the association scheme.

spaces := Eigenspaces(Rationals,Assoc[4]);;
Pmat := NullMat(7,7);;
for j in [1..7] do
  Pmat[j,1] := 1;
  v := Random(spaces[j]);
  for i in [1..6] do
    Pmat[j,i+1] := (v*Assoc[i]*v) / (v*v);
  od;
od;
Pmat;

# We verify that the full automorphism group of the graph Gamma* is isomorphic to G.
# We already know that G is isomorphic to Sym7.

gammastar := Graph( G, spreads, OnSetsProjSubspaces, function( s, t ) if relation( spreadsort( s ), spreadsort( t ) ) in [3,4,6] then return true; else return false; fi; end);;
aut := AutGroupGraph( gammastar );;
IsomorphismGroups( aut, SymmetricGroup( 7 ) );
IsomorphismGroups( aut, G );

# This proves Theorem 3.2, except for the fact that the union of relations 5 and 6 is isomorphic to the complement graph of NO+(8,2).
# This isomorphism follows easily from Theorem 4.3 that we will prove below.

# Next, we verify Remark 3.4 by constructing Table 2.

table2 := List([1,2], i -> List([1,2], j -> []));;
for rep in reps do
  if not rep = spr1 then
    i := Size( Intersection( rep{[1,2]},  spr1{[1,2]} )) + 1;
    j := Size( Intersection( rep{[3..9]}, spr1{[3..9]} )) + 1;
    Add( table2[i,j], relation( rep, spr1 ) );
  fi;
od;
table2;

##################
#                #
#     OVOIDS     #
#                #
##################


# Our next goal is to prove Theorem 4.3.
# We start by fixing a spread, taking G to be the setwise stabiliser of the spread and a subset of 2 generators,
# and considering orbit of size 120 on the ovoids.

G := FiningSetwiseStabiliser( pgo, spread );;
G := FiningSetwiseStabiliser( G, spread{[1,2]} );;
allovoids := Set( FiningOrbit( pgo, Set(ov), OnSetsProjSubspaces ));;
ovoids := Filtered( FiningOrbits( G, allovoids, OnSetsProjSubspaces ), orb -> Size(orb) = 120)[1] ;;

# We store the union of the points in the first two generators of spread in spreadpts.
# The function pttoov takes an anisotropic point and returns the corresponding ovoid.

spreadpts := Union(Points(spread[1]),Points(spread[2]));;
pttoov := function(P)
  local ovoid;
  return Filtered(ovoids, ovoid -> P*Span( Intersection( ovoid, spreadpts ) ))[1]; 
end;;

# We store the anisotropic points in a list.
# We fix one anisotropic point P, let Gstab be its stabiliser in G, and choose representatives for the orbits of Gstab.

anisotropic := Filtered( List( Points( PG(7,2) )), P -> not P in Points( quad ));;
P := anisotropic[1];;
Gstab := FiningStabiliser( G, P );;
orbs := FiningOrbits( Gstab, anisotropic );;
reps := List( orbs, orb -> orb[1] );;

# We check that two anisotropic points P and Q are orthogonal if and only if their ovoids intersect.
# Since both properties are G-invariant, it suffices to fix one anisotropic point P, and check this property
# with respect to a representative Q of each orbit of the stabiliser in G of P.

perp := PolarityOfProjectiveSpace( quad );;
check := true;;
for Q in reps do
  if not Q = P then
    areOrtho := P * Q^perp;
    disjoint := ( Intersection( pttoov(Q), pttoov(P) ) = [] );
    if ( ( areOrtho and disjoint ) or ( ( not areOrtho ) and ( not disjoint ) ) ) then
      check := false;
    fi;
  fi;
od;
check;

# We introduce a function relation that takes two anisotropic points P and Q and returns the relation containing (P,Q)
# as defined in Theorem 4.3.
# We introduce a function thirdpoint that takes two distinct points as argument, and returns the third point on the line spanned by the first two.

thirdpoint := function(P,Q)
  local L, res, R;
  L := Span(P,Q);
  res := Filtered(Points(L), R -> not R in [P,Q])[1];
  return res;
end;;

relation := function(P,Q)
  local ovoid, intersect, R, res;
  res := "nothing";
  if P = Q then
     res := 0;
  else
    ovoid := pttoov(P);
    intersect := Size( Filtered( ovoid, R -> R * Q^perp ));;
    if P * Q^perp then
      R := thirdpoint(P,Q);
      if intersect = 3 then
        if R in ovoid then
          res := 1;
        elif R in spreadpts then
          res := 2;
        else
          res := 3;
        fi;
      else
        if not R in spreadpts then
          res := 4;
        fi;
      fi;
    else  
      if intersect = 3 then
        res := 5;
      else
        res := 6;
      fi;
    fi;
  fi;
  return res;
end;;

# We check that for every representative Q in reps, relation(P,Q) is one of the defined relations, and relation(P,Q)
# distinguishes the points in reps.

List( reps, Q -> relation(P,Q) );

# Therefore, the relations must define an association scheme.
# This association scheme must be isomorphic to the one from Theorem 3.3.
# To prove that the isomorphism respect the order of the relations, it suffices to prove that the matrices of eigenvalues coincide,
# since for each relation i of the scheme, the multiset of entries in the ith column of Pmat is different.

Assoc := List([1..6], i -> NullMat(120,120));;
for i in [1..120] do
  for j in [1..120] do
    k := relation( anisotropic[i], anisotropic[j] );
    if not k = 0 then
      Assoc[k][i,j] := 1;
    fi;
  od;
od;
spaces := Eigenspaces(Rationals,Assoc[4]);;
Pmat2 := NullMat(7,7);;
for j in [1..7] do
  Pmat2[j,1] := 1;
  v := Random(spaces[j]);
  for i in [1..6] do
    Pmat2[j,i+1] := (v*Assoc[i]*v) / (v*v);
  od;
od;
Set(Pmat) = Set(Pmat2);

# This settles the proof of Theorem 4.3.
# Note that it is trivially true that the union of relations 5 and 6 yields the complement graph of NO+(8,2).


#####################
#                   #
#     COCLIQUES     #
#                   #
#####################

# We define the graph Gamma* using the representation from Theorem 4.3.
# comp is its complement graph.

gammastar := Graph( G, anisotropic, OnProjSubspaces, function( P, Q ) if relation( P, Q ) in [3, 4, 6] then return true; else return false; fi; end);;
comp := ComplementGraph( gammastar );;

# cocliquereps contains a unique representative of each orbit of G on the maximum cocliques of gammastar (or equivalently the maximum cliques of comp).
# aut is the Automorphism group of gammastar.
# We check the size of the orbits of aut on the maximum cocliques.
# This proves Proposition 5.1 (1).

cocliquereps := CompleteSubgraphs( comp, 8, 2 );;
aut := AutGroupGraph( gammastar );;
List( cocliquereps, c -> Size( Orbit( aut, c, OnSets ) ) );

# We order the cocliques in ascending orbit size, to match the order in the paper.

cocliquereps  := List( [1..3], i -> Filtered( cocliquereps, c -> Size( Orbit( aut, c, OnSets ) ) = [30, 120, 210][i] )[1] );;

# For each coclique representative, we check in how many ways it is intersected by the neighbourhoods of the vertices outside the coclique.
# This proves Proposition 5.1 (2).

List( cocliquereps, c -> Size( Unique( List( Difference( [1..120], c ), i -> Intersection( c, Adjacency( gammastar, i ) ) ))) );

# We verify Proposition 5.1 (3).
# First, we build a coclique as described and prove that it is in the same aut-orbit as cocliquereps[1].
# Since G is the full automorphism group of gammastar, and acts transitively on the points in Sigma1 union Sigma2,
# the structural description of the cocliques in this orbit follows.

Q := List(Points( spread[1] ))[1];;
C := List( Filtered( Points( spread[2]) , R -> not R * Q^perp ), R -> thirdpoint(R, Q) );;
c := Filtered([1..120], i -> VertexName( gammastar, i ) in C );;
c in Orbit( aut, cocliquereps[1], OnSets );

# Next, we check that if we take two points Q and Q’ in Sigma1, then the neighbourhoods of the vertices in C_{1,Q’}
# all intersect C_{1,Q} in a different way. We first check that the stabiliser of Q in G acts transitively on the other points of
# Sigma1, so that it suffices to check only one choice of Q’.

Q2 := List(Points( spread[1] ))[2];;
Size( FiningOrbit( FiningStabiliser( G, Q ), Q2 )) = 14;
C2 := List( Filtered( Points( spread[2]) , R -> not R * Q2^perp ), R -> thirdpoint(R, Q2) );;
c2 := Filtered([1..120], i -> VertexName( gammastar, i ) in C2 );;
Size(Set( c2, i -> Intersection( c, Adjacency( gammastar, i ) ) )) = 8;

# To prove Proposition 5.1 (4), it suffices to prove that a representative C of the second orbit of cocliques contains a point P
# such that all other points in C are in relation 1 with respect to P, and relation 5 with each other.

C := Set( cocliquereps[2], i -> VertexName( gammastar, i ));;
List( C, P -> List( C, Q -> relation(P,Q) ));

# To prove Proposition 5.1 (5), we make a graph gammacocl on the maximum cocliques of gammastar, where the adjacency relation is
# sharing at most one vertex. We show that the clique number of this graph is 66.

allcocliques := Union( List( cocliquereps, c -> Orbit( aut, c, OnSets ) ));;
gammacocl := Graph( aut, allcocliques, OnSets, function( c, d ) if Size( Intersection( c, d) ) < 2 then return true; else return false; fi; end);;
CliqueNumber(gammacocl);
