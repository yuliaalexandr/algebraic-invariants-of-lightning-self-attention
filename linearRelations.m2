-* linearRelations.m2

Construct the linear relations in the fixed coefficient slice extracted in the
main file.

Assumptions:
  1. The main file has already defined d, t, j, idxList, and the ambient ring L.
  2. Coefficients were extracted from the output coordinate with fixed target column j.
  3. We work in the case d' = 1.

Output:
  makeLinearRelations(L,idxList,d,t,j) returns the list of linear relations in L.

The relations are:
  - cross-context sequence-copy relations
  - internal symmetrization relations
*-

makeLinearRelations = (L,idxList,d,t,j) -> (

    -- multisets of size 2 from [d]
    pairs2 := {};
    for a from 1 to d do
        for b from a to d do
            pairs2 = append(pairs2,{a,b});

    -- multisets of size 3 from [d]
    triples3 := {};
    for a from 1 to d do
        for b from a to d do
            for c from b to d do
                triples3 = append(triples3,{a,b,c});

    -- indices in the same format as idxList
    singleIdx := (K,j) -> toSequence sort apply(K, k -> (k,j));
    crossIdx := (A,b,n,j) -> toSequence sort append(apply(A, a -> (a,n)), (b,j));

    -- lookup: index -> variable in L
    yVar := idx -> sub(y_idx, L);

    -- orbit sizes
    permSize2 := A -> if A#0 == A#1 then 1 else 2;

    permSize3 := K -> (
        if K#0 == K#1 and K#1 == K#2 then 1
        else if K#0 == K#1 or K#1 == K#2 then 3
        else 6
    );

    -- distinct decompositions K = A union {b}, where |A| = 2
    decomps3 := K -> unique {
        {{K#1,K#2}, K#0},
        {{K#0,K#2}, K#1},
        {{K#0,K#1}, K#2}
    };

    rels := {};

    -- if t = 1, there are no cross-column variables
    if t == 1 then return rels;

    -- cross-context sequence-copy relations
    if t >= 3 then (
        otherCols := select(toList(1..t), n -> n =!= j);
        for u from 0 to #otherCols-1 do (
            for v from u+1 to #otherCols-1 do (
                n := otherCols#u;
                n' := otherCols#v;
                for A in pairs2 do (
                    for b from 1 to d do (
                        rels = append(rels,
                            yVar(crossIdx(A,b,n,j)) - yVar(crossIdx(A,b,n',j))
                        )
                    )
                )
            )
        )
    );

    -- internal symmetrization relations
    for n in select(toList(1..t), n -> n =!= j) do (
        for K in triples3 do (
            rels = append(rels,
                permSize3(K) * yVar(singleIdx(K,j))
                - sum apply(decomps3(K), db ->
                    permSize2(db#0) * yVar(crossIdx(db#0, db#1, n, j))
                )
            )
        )
    );

    rels
);