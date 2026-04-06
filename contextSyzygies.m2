-* contextSyzygies.m2

Construct the cross-context determinantal syzygies for a fixed target column j
and all context columns n != j.

This file directly generalizes the working code for d=3:
  1. Build the formal flattening matrix F_{n,j}.
  2. Build the model matrix Phi(v).
  3. Compute all maximal minors of both.
  4. Form the coefficient matrix of the model minors in the degree-d monomial basis.
  5. Compute the kernel of that coefficient matrix.
  6. Apply the kernel vectors to the formal minors.

Assumptions:
  1. The main file has already defined d, t, idxList, and the ambient ring L.
  2. We work in the case d' = 1.
  3. The target column j is passed as an argument.
  4. The y-variables are the last #idxList generators of L.
*-

makeContextSyzygies = (L,idxList,d,t,j) -> (

    if j < 1 or j > t then error("j must lie in [1..t]");

    ------------------------------------------------------------
    -- unordered pairs {a,b} with 1 <= a <= b <= d
    ------------------------------------------------------------

    pairs2 := {};
    for a from 1 to d do
        for b from a to d do
            pairs2 = append(pairs2,{a,b});

    ------------------------------------------------------------
    -- row subsets for maximal minors of a D x d matrix
    ------------------------------------------------------------

    rowSets := subsets(toList(0..(#pairs2-1)), d);
    allMaxMinors := M -> apply(rowSets, R -> det submatrix(M,R,toList(0..(d-1))));

    ------------------------------------------------------------
    -- lookup of coefficient variables in L using idxList
    ------------------------------------------------------------

    offset := numgens L - #idxList;

    crossLabel := (a,b,c,n,j) -> toSequence sort {(a,n),(b,n),(c,j)};

    idx := (a,b,c,n,j) -> (
        p := position(idxList, lab -> lab == crossLabel(a,b,c,n,j));
        if p === null then error("monomial label not found in idxList");
        p
    );

    coeffVar := (a,b,c,n,j) -> (gens L)_(offset + idx(a,b,c,n,j));

    ------------------------------------------------------------
    -- model matrix Phi(v)
    ------------------------------------------------------------

    Kv := QQ[apply(toList(1..d), r -> v_r)];
    vv := gens Kv;

    phiEntry := (a,b,c) -> (
        if a == b then (
            if c == a then vv#(a-1) else 0_Kv
        )
        else (
            if c == a then vv#(b-1)/2
            else if c == b then vv#(a-1)/2
            else 0_Kv
        )
    );

    Phi := matrix apply(pairs2, A ->
        apply(toList(1..d), c -> phiEntry(A#0,A#1,c))
    );

    mPhi := allMaxMinors Phi;

    ------------------------------------------------------------
    -- coefficient matrix of the model minors
    ------------------------------------------------------------

    mons := flatten entries basis(d,Kv);

    Cphi := transpose matrix apply(mPhi, f ->
        apply(mons, m -> coefficient(m,f))
    );

    Kphi := gens kernel Cphi;

    ------------------------------------------------------------
    -- apply the kernel vectors to the formal minors of F_{n,j}
    ------------------------------------------------------------

    rels := {};

    for n from 1 to t do (
        if n =!= j then (
            Fnj := matrix apply(pairs2, A ->
                apply(toList(1..d), c -> coeffVar(A#0,A#1,c,n,j))
            );

            mF := allMaxMinors Fnj;
            rels = append(rels, flatten entries (matrix{mF} * sub(Kphi,L)));
        )
    );

    flatten rels
);