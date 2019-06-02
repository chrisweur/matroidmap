-*-------------------------------------------------------------------------------------------
Computations for Log-concavity for morphisms of matroids

Author: Christopher Eur
Last update: 5/12/2019
------------------------------------------------------------------------------------------*-

needsPackage "Matroids"

--tests whether a matroid m is a quotient of a matroid n
isQuot = (m,n) -> isSubset(flats m, flats n)

--Las Vergnas Tutte polynomial of a matroid quotient
LVTutte = method();
LVTutte(Matroid,Matroid,Ring) := RingElement => (M,N,R) -> (
    if M.groundSet === set{} then return 1_R;
    lM := loops M; clM := coloops M;
    lN := loops N; clN := coloops N;
    e := set {0};
    if member(0,lN) then return R_1*LVTutte(M \ e, N \ e, R);
    if member(0,clM) then return R_0*LVTutte(M \ e, N \ e, R);
    if member(0,clN) and not member(0,clM) then return R_2*LVTutte(M\e,N\e,R) + LVTutte(M/e,N/e,R);
    LVTutte(M\e,N\e,R) + LVTutte(M/e,N/e,R)
)

LVTutte(Matroid,Matroid) := RingElement => (M,N) -> (
    x := symbol x;
    y := symbol y;
    z := symbol z;
    R := ZZ[x,y,z];
    LVTutte(M,N,R)
)

--basis generating polynomial of a matroid quotient m <<-- n
bases(Matroid,Matroid) := (m,n) -> (
    r := rank m; s := rank n;
    t := symbol t; R := QQ[t];
    sum(toList(r..s), i -> #select(independentSets(n,i), j -> any(bases m, b -> isSubset(b,j))) * R_0^i)
    )



end


-------------------------------------------------------------------------------------------
-------------------------------------- COMPUTATIONS----------------------------------------
restart
load "LogConcMatMorph.m2"


--------------< the 1-skeleton of prism collapsing to a triangle example >-----------------
G = graph{{A,B},{B,C},{C,A},{a,b},{b,c},{c,a},{A,c},{B,a},{C,b}}
edges G
CG = matroid G
HParallels = {set{0,4,6},set{3,5,8},set{1,2,7}}
B = (flatten (apply(subsets(HParallels,2), l -> (first l) ** (last l))/elements))/toList
CH = matroid(toList(0..8), B)
isQuot(CH,CG)
bases(CH,CG)


------------------< Petersen graph 3-coloring example >---------------------
--see https://en.wikipedia.org/wiki/File:Petersen_graph_3-coloring.svg
G = generalizedPetersenGraph (5,2)
M = matroid G
P = {{0,2,8,9},{1,4,5},{3,6,7}}/set
B = select(subsets(15,2), s -> (S :=  M_(first s) + M_(last s); all(P, p -> #(S * p) > 0)))
N = matroid(toList(0..14), B)
isQuot(N,M)
bases(N,M)


----------------------< The M(K7) <-- M^*(Heawood graph) example >-------------------------

--the triangulation of the torus with 7 vertices and 14 2-cells
T = {{a,c,d},{a,b,d},{b,d,e},{b,c,e},{c,e,f},{c,d,f},{f,d,g},{d,g,e},{e,a,g},{a,e,f},{a,b,f},{b,f,g},{b,c,g},{a,c,g}}/set
T === unique T, #T --checking

--the 1-cells (ridges) defined by intersection of 2-cells
Tridges = select(subsets(T,2), i -> #((first i) * (last i)) == 2)
--indices of the 2-cells defining the ridges
TridgesIndices = Tridges/(r -> r/(i -> position(T, j -> j===i)))
H = graph TridgesIndices --the Heawood graph
MH = matroid H

--the edges of the triangulation T is K7
Tedges = unique flatten apply(T, c -> subsets(c,2))
K = graph Tedges
MK = matroid K

--the elements of MH, which are ridges in T, have edge names
MHEdgeNames = (MH_*)/(i -> product ((elements i)/(j -> T_j)))

--the i-th element of MH_* has index toMKIndex(i) in MK_*
toMKIndex = i -> position(MK_*, j -> (MHEdgeNames)_i === j)
toMKIndex 0, MHEdgeNames_0, (MK_*)_6 --checking

time B = apply(bases MH, b -> b/toMKIndex); -- 4.5 seconds
MHFinal = matroid(toList(0..20), B) --the Heawood graph matroid, relabeled appropriately

time flats MK; --2 seconds
time flats (dual MHFinal); --21 seconds
time isQuot(MK, dual MHFinal) --checking that we do have a matroid quotient

#bases (dual MHFinal)
#bases MK
time I = independentSets(dual MHFinal,7); --3 seconds
time f7 = #select(I, i -> any(bases MK, b -> isSubset(b,i))) --2040 seconds on Berkeley computing server

--the dumb way: time bases(MK, dual MHFinal) --5060 seconds on Berkeley computing server
ZZ[t]; 50421*t^8+47715*t^7+16807*t^6 --the result
47715^2 > 50421 * 16807 * 15 / 14 * 8 / 7 -- checking ultra-log-concavity

--------------------------< A^4 --> P^2 example >--------------------------

(toList({0,0,0,0}..{1,1,1,1}))/(l -> l | {1})
A = matrix transpose oo
F = ZZ/2;
A = (sub(A,F))_(toList(2..15))

M = matroid A^{0,1,2}
N = matroid A
isQuot(M,N)
bases(M,N)
840^2 > 5 * 13 * 224 * 1232 / 4 / 12





