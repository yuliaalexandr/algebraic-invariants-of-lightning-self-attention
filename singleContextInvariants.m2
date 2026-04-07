-- ============================================================
-- singleContextInvariants.m2
--
-- Invariants for the t = 1 (single-context) case.
--
-- Families implemented:
--   1. Low-rank minors of the matrix N = (y_{k,k,l})_{k,l},
--      coming from rank(N) <= 2*at + 1.
--   2. Chow-type Lie flattening minors for the split (2,1) locus.
--
-- Notes:
--   * Assumes d' = 1 and t = 1.
--   * Low-rank and Chow-type families can be generated separately.
--   * This file does NOT implement Brill equations for the full
--     Chow variety of split type (1,1,1).
-- ============================================================

------------------------------------------------------------
-- Small helpers
------------------------------------------------------------

makeIdealFromList = (R, rels) -> (
    if #rels == 0 then ideal(0_R)
    else trim ideal select(rels, f -> f =!= 0_R)
);

quarticCount = I -> #select(flatten entries mingens I, f -> degree f == {4});

unorderedTriplezWithRep = d -> (
    T := {};
    for i from 1 to d do (
        for j from i to d do (
            for k from j to d do (
                T = append(T, toSequence {i,j,k});
            )
        )
    );
    T
);

orbitSize3 = lab -> (
    if lab#0 == lab#2 then 1
    else if lab#0 == lab#1 or lab#1 == lab#2 then 3
    else 6
);

coeffVarSingle = (myRing, idxList, i, j, k) -> (
    idxL := toList idxList;
    lab := toSequence sort {i,j,k};
    p := position(idxL, s -> s === lab);
    if p === null then error("label not found: " | toString lab);
    (gens myRing)_p
);

labelFromMon = (T, mon) -> (
    toSequence sort flatten apply(#gens T, r ->
        toList((exponents mon)_0_r : (r+1))
    )
);

------------------------------------------------------------
-- Single-context cubic
------------------------------------------------------------

makeSingleContextPolynomial = (myRing, idxList, d) -> (
    T := myRing[x_1..x_d];
    xVars := apply(0..d-1, r -> (gens T)_r);
    cubicLabels := unorderedTriplezWithRep(d);

    f := 0_T;
    for lab in cubicLabels do (
        f = f
          + orbitSize3(lab)
            * sub(coeffVarSingle(myRing, idxList, lab#0, lab#1, lab#2), T)
            * product apply(toList lab, kk -> xVars#(kk-1));
    );

    {T, xVars, cubicLabels, f}
);

------------------------------------------------------------
-- Low-rank family
------------------------------------------------------------

makeSingleContextLowRankMatrix = (myRing, idxList, d) -> (
    matrix(
        apply(toList(1..d), k ->
            apply(toList(1..d), ell -> coeffVarSingle(myRing, idxList, k, k, ell))
        )
    )
);

makeSingleContextLowRankIdeal = (myRing, idxList, d, at) -> (
    N := makeSingleContextLowRankMatrix(myRing, idxList, d);
    m := 2*at + 2;
    if m > d then ideal(0_myRing) else trim minors(m, N)
);

------------------------------------------------------------
-- Lie flattening family for split (2,1)
------------------------------------------------------------

coeffVectorCubic = (myRing, T, cubicLabels, g) -> (
    mons := flatten entries ((coefficients g)_0);
    coeffs := flatten entries ((coefficients g)_1);

    H := new MutableHashTable;
    if #mons > 0 then (
        scan(0..#mons-1, p -> (
            H#(labelFromMon(T, mons#p)) = sub(coeffs#p, myRing);
        ));
    );

    apply(cubicLabels, lab -> (
        if H#?lab then H#lab else 0_myRing
    ))
);

makeSingleContextLieMatrix = (myRing, idxList, d) -> (
    data := makeSingleContextPolynomial(myRing, idxList, d);
    T := data#0;
    xVars := data#1;
    cubicLabels := data#2;
    f := data#3;

    actionPolys := {};

    -- diagonal basis H_u = E_uu - E_dd, u = 1,...,d-1
    for u from 1 to d-1 do (
        actionPolys = append(actionPolys,
            xVars#(u-1) * diff(xVars#(u-1), f)
          - xVars#(d-1) * diff(xVars#(d-1), f)
        );
    );

    -- off-diagonal basis E_uv = x_u d/dx_v, u != v
    for u from 1 to d do (
        for v from 1 to d do (
            if u =!= v then (
                actionPolys = append(actionPolys,
                    xVars#(u-1) * diff(xVars#(v-1), f)
                );
            );
        );
    );

    colVecs := apply(actionPolys, g -> coeffVectorCubic(myRing, T, cubicLabels, g));
    transpose matrix(colVecs)
);

makeSingleContextLieIdeal = (myRing, idxList, d) -> (
    M := makeSingleContextLieMatrix(myRing, idxList, d);
    colCount := d^2 - 1;
    rowCount := binomial(d+2, 3);
    if rowCount < colCount then ideal(0_myRing) else trim minors(colCount, M)
);

------------------------------------------------------------
-- Combined wrapper
------------------------------------------------------------

makeSingleContextInvariants = (myRing, idxList, d, at) -> (
    H := new MutableHashTable;

    H#"N" = makeSingleContextLowRankMatrix(myRing, idxList, d);
    H#"lowRank" = makeSingleContextLowRankIdeal(myRing, idxList, d, at);

    H#"MLie" = makeSingleContextLieMatrix(myRing, idxList, d);
    H#"split21" = makeSingleContextLieIdeal(myRing, idxList, d);

    H#"all" = trim(H#"lowRank" + H#"split21");
    H
);