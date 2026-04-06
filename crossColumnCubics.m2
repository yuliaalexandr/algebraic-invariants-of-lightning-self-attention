-* crossColumnCubics.m2

Construct the cubic invariants from Proposition prop:cross-column for a fixed
target column j and all context columns n != j.

Assumptions:
  1. The main file has already defined d, t, j, and the ambient ring L.
  2. We work in the case d' = 1.
  3. The variables of L are the coefficient variables y_idx for the fixed
     output coordinate chosen in the main file.

Output:
  makeCrossColumnCubics(L,d,t,j) returns the list of cubic relations in L.

Method:
  For each context column n != j and each target index k in [d], form the
  symmetric slice
      M_{n,j}^{(k)} = ( y_{(r,n),(s,n),(k,j)} )_{r,s in [d]}.
  Then form the matrix pencil
      M(c) = c_1 M_{n,j}^{(1)} + ... + c_d M_{n,j}^{(d)}.
  Since every 3x3 minor of M(c) vanishes, its coefficients in the dummy
  variables c_1,...,c_d give cubic relations among the y-variables.

Notes:
  1. If d < 3, there are no 3x3 minors, so the function returns the empty list.
  2. The function internally loops over all context columns n != j.
*-

makeCrossColumnCubics = (L,d,t,j) -> (

    if j < 1 or j > t then error("j must lie in [1..t]");

    -- no 3x3 minors if d < 3
    if d < 3 then return {};

    -- index in the same format as idxList from the main file
    crossIdx := (A,b,n,j) -> toSequence sort append(apply(A, a -> (a,n)), (b,j));

    -- variable lookup in L
    yVar := idx -> sub(y_idx, L);

    rels := {};

    -- loop over all context columns n != j
    for n from 1 to t do (
        if n =!= j then (

            -- slices M_{n,j}^{(k)}, k = 1,...,d
            slices := for k from 1 to d list matrix(
                for r from 1 to d list
                    for s from 1 to d list
                        yVar(crossIdx(sort {r,s}, k, n, j))
            );

            -- dummy variables for the matrix pencil
            Sdum := L[c_1..c_d];

            -- build M(c) = sum_k c_k M^{(k)}
            M := sum(d, k -> c_(k+1) * sub(slices#k, Sdum));

            -- extract coefficients of all 3x3 minors with respect to c_1,...,c_d
            rels = flatten append(rels,
                flatten entries sub((coefficients(gens minors(3, M), Variables => gens Sdum))#1, L)
            );
        )
    );

    rels
);