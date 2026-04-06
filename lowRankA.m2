-* lowRankA.m2

Construct the low-rank-A invariants for a fixed target column j and all
context columns n != j.

Assumptions:
  1. The main file has already defined d, t, at, j, and the ambient ring L.
  2. We work in the case d' = 1.
  3. The variables of L are the coefficient variables y_idx for the fixed
     output coordinate chosen in the main file.

Output:
  makeLowRankA(L,d,t,at,j) returns the list of all (at+1)x(at+1) minors of the
  flattening matrices F_{n,j}, taken over every context column n != j.

Notes:
  1. For each n != j, the rows of F_{n,j} are indexed by unordered pairs
     {k1,k2} with 1 <= k1 <= k2 <= d.
  2. The columns of F_{n,j} are indexed by l in [d].
  3. The ({k1,k2}, l) entry is y_{(k1,n),(k2,n),(l,j)}.
  4. If at >= d, there are no nontrivial low-rank-A relations, and the
     function returns the empty list.
*-

makeLowRankA = (L,d,t,at,j) -> (

    if j < 1 or j > t then error("j must lie in [1..t]");

    -- no nontrivial minors if at >= d
    if at >= d then return {};

    -- unordered pairs {k1,k2} from [d]
    pairs2 := {};
    for a from 1 to d do
        for b from a to d do
            pairs2 = append(pairs2,{a,b});

    -- index in the same format as idxList from the main file
    crossIdx := (A,b,n,j) -> toSequence sort append(apply(A, a -> (a,n)), (b,j));

    -- variable lookup in L
    yVar := idx -> sub(y_idx, L);

    rels := {};

    -- build F_{n,j} for every n != j and collect all (at+1)x(at+1) minors
    for n from 1 to t do (
        if n =!= j then (
            F := matrix apply(pairs2, A ->
                    apply(toList(1..d), l -> yVar(crossIdx(A,l,n,j)))
                );
            rels = flatten append(rels, flatten entries gens minors(at+1, F));
        )
    );

    rels
);