-* sliceResultantQuartics.m2

Generate quartic invariants from resultants of slice quadrics restricted to a line.

Setup:
  Fix a target column j and a context column n != j. For each slice index s in [d],
  form the ternary quadric
      q_s(x) = sum_{1 <= u <= v <= d} omega(u,v) y_{(u,n),(v,n),(s,j)} x_u x_v,
  where omega(u,v) = 1 if u=v and 2 otherwise.

  Restrict these quadrics to a fixed line
      x = a*s + b*t,
  where a,b in Z^d are supplied by the user. Each restricted quadric has the form
      q_s|_L = A_s s^2 + B_s s t + C_s t^2.

Families implemented:
  1. Pairwise slice-resultants:
     For each unordered pair of slices {i,k}, take
         Res(q_i|_L, q_k|_L).
     This gives quartic invariants.

  2. Triple-slice resultant coefficients:
     For each unordered triple of slices {i,j,k}, consider two generic linear
     combinations of the three restricted binary quadrics and extract the six
     coefficients of type
         u_i^2 v_j v_k, u_j^2 v_i v_k, u_k^2 v_i v_j,
         u_i u_j v_k^2, u_i u_k v_j^2, u_j u_k v_i^2.
     These are quartic invariants.

Assumptions:
  1. The main file has already defined:
       - the ambient coefficient ring L = QQ[y_idx],
       - idxList,
       - d, t, at, j.
  2. We work in the case d' = 1.
  3. The parameter at is not used here; it is included only for interface
     compatibility with other files.

Notes:
  1. These constructions produce quartics for any d,t,at, because they are built
     from resultants of binary quadrics.
  2. For d=3, these families recovered the extra quartics beyond the previously
     known local families in the small example.
  3. For larger d, this file generates a natural quartic subfamily; completeness
     is not asserted.

*-

------------------------------------------------------------
-- Small helpers
------------------------------------------------------------

makeIdealFromList = (R, rels) -> (
    if #rels == 0 then ideal(0_R)
    else trim ideal select(rels, f -> f =!= 0_R)
);

quarticCount = I -> #select(flatten entries mingens I, f -> degree f == {4});

unorderedPairzWithRep = d -> (
    P := {};
    for u from 1 to d do (
        for v from u to d do (
            P = append(P, {u,v});
        )
    );
    P
);

unorderedPairz = d -> (
    P := {};
    for u from 1 to d-1 do (
        for v from u+1 to d do (
            P = append(P, {u,v});
        )
    );
    P
);

unorderedTriplez = d -> (
    T := {};
    for u from 1 to d-2 do (
        for v from u+1 to d-1 do (
            for w from v+1 to d do (
                T = append(T, {u,v,w});
            )
        )
    );
    T
);

coeffVar = (myRing, idxList, u, v, slice, n, j) -> (
    lab := toSequence sort {(u,n),(v,n),(slice,j)};
    p := position(idxList, s -> s === lab);
    if p === null then error("label not found: " | toString lab);
    (gens myRing)_p
);

-- Restrict q_slice(x) to the line x = a*s + b*t.
-- Returns {A,B,C} with q_slice|_L = A*s^2 + B*s*t + C*t^2.
restrictedABC = (myRing, idxList, d, t, j, a, b, slice, n) -> (
    if #a =!= d then error("a must have length d");
    if #b =!= d then error("b must have length d");

    AA := 0_myRing;
    BB := 0_myRing;
    CC := 0_myRing;

    pairzUV := unorderedPairzWithRep(d);

    for pr in pairzUV do (
        u := pr#0;
        v := pr#1;
        wt := if u == v then 1 else 2;
        y := coeffVar(myRing, idxList, u, v, slice, n, j);

        AA = AA + wt * y * (a#(u-1)) * (a#(v-1));
        BB = BB + wt * y * ((a#(u-1))*(b#(v-1)) + (b#(u-1))*(a#(v-1)));
        CC = CC + wt * y * (b#(u-1)) * (b#(v-1));
    );

    {AA, BB, CC}
);

------------------------------------------------------------
-- Binary resultant formulas
------------------------------------------------------------

binaryQuadraticResultant = (A1, B1, C1, A2, B2, C2) -> (
    det matrix{
        {A1, B1, C1, 0_(ring A1)},
        {0_(ring A1), A1, B1, C1},
        {A2, B2, C2, 0_(ring A1)},
        {0_(ring A1), A2, B2, C2}
    }
);

-- Coefficient of u_i^2 v_j v_k in
-- Res(sum u_r q_r, sum v_r q_r)
coeff211 = (A, B, C, i, j1, k1) -> (
    Ai := A#(i-1); Aj := A#(j1-1); Ak := A#(k1-1);
    Bi := B#(i-1); Bj := B#(j1-1); Bk := B#(k1-1);
    Ci := C#(i-1); Cj := C#(j1-1); Ck := C#(k1-1);

      2*Ai^2*Cj*Ck
    - 2*Ai*Aj*Ci*Ck
    - 2*Ai*Ak*Ci*Cj
    - Ai*Bi*Bj*Ck
    - Ai*Bi*Bk*Cj
    + 2*Ai*Bj*Bk*Ci
    + 2*Aj*Ak*Ci^2
    + Aj*Bi^2*Ck
    - Aj*Bi*Bk*Ci
    + Ak*Bi^2*Cj
    - Ak*Bi*Bj*Ci
);

-- Coefficient of u_i u_j v_k^2 in
-- Res(sum u_r q_r, sum v_r q_r)
coeff112 = (A, B, C, i, j1, k1) -> (
    Ai := A#(i-1); Aj := A#(j1-1); Ak := A#(k1-1);
    Bi := B#(i-1); Bj := B#(j1-1); Bk := B#(k1-1);
    Ci := C#(i-1); Cj := C#(j1-1); Ck := C#(k1-1);

      2*Ai*Aj*Ck^2
    - 2*Ai*Ak*Cj*Ck
    - Ai*Bj*Bk*Ck
    + Ai*Bk^2*Cj
    - 2*Aj*Ak*Ci*Ck
    - Aj*Bi*Bk*Ck
    + Aj*Bk^2*Ci
    + 2*Ak^2*Ci*Cj
    + 2*Ak*Bi*Bj*Ck
    - Ak*Bi*Bk*Cj
    - Ak*Bj*Bk*Ci
);

------------------------------------------------------------
-- Triple-slice resultant quartics on one line
------------------------------------------------------------

makeTripleSliceResultantQuarticsOnLine = (myRing, idxList, d, t, at, j, a, b) -> (
    if #a =!= d then error("a must have length d");
    if #b =!= d then error("b must have length d");
    if j < 1 or j > t then error("j must lie in [1..t]");

    rels := {};
    sliceTriplez := unorderedTriplez(d);

    for n from 1 to t do (
        if n =!= j then (
            A := {};
            B := {};
            C := {};

            for slice from 1 to d do (
                abc := restrictedABC(myRing, idxList, d, t, j, a, b, slice, n);
                A = append(A, abc#0);
                B = append(B, abc#1);
                C = append(C, abc#2);
            );

            for tr in sliceTriplez do (
                i := tr#0;
                k := tr#1;
                ell := tr#2;

                rels = append(rels, coeff211(A,B,C,i,k,ell));
                rels = append(rels, coeff211(A,B,C,k,i,ell));
                rels = append(rels, coeff211(A,B,C,ell,i,k));

                rels = append(rels, coeff112(A,B,C,i,k,ell));
                rels = append(rels, coeff112(A,B,C,i,ell,k));
                rels = append(rels, coeff112(A,B,C,k,ell,i));
            );
        )
    );

    makeIdealFromList(myRing, rels)
);

------------------------------------------------------------
-- Pairwise slice-resultant quartics on one line
------------------------------------------------------------

makePairSliceResultantQuarticsOnLine = (myRing, idxList, d, t, at, j, a, b) -> (
    if #a =!= d then error("a must have length d");
    if #b =!= d then error("b must have length d");
    if j < 1 or j > t then error("j must lie in [1..t]");

    rels := {};
    slicePairz := unorderedPairz(d);

    for n from 1 to t do (
        if n =!= j then (
            ABC := {};

            for slice from 1 to d do (
                ABC = append(ABC, restrictedABC(myRing, idxList, d, t, j, a, b, slice, n));
            );

            for pr in slicePairz do (
                i := pr#0;
                k := pr#1;

                Ai := (ABC#(i-1))#0;
                Bi := (ABC#(i-1))#1;
                Ci := (ABC#(i-1))#2;

                Ak := (ABC#(k-1))#0;
                Bk := (ABC#(k-1))#1;
                Ck := (ABC#(k-1))#2;

                rels = append(rels, binaryQuadraticResultant(Ai,Bi,Ci,Ak,Bk,Ck));
            );
        )
    );

    makeIdealFromList(myRing, rels)
);

------------------------------------------------------------
-- Both families on one line
------------------------------------------------------------

makeSliceResultantQuarticsOnLine = (myRing, idxList, d, t, at, j, a, b) -> (
    trim(
        makeTripleSliceResultantQuarticsOnLine(myRing, idxList, d, t, at, j, a, b)
      + makePairSliceResultantQuarticsOnLine(myRing, idxList, d, t, at, j, a, b)
    )
);

------------------------------------------------------------
-- Sum families over a user-supplied list of lines
------------------------------------------------------------

tripleSliceResultantQuarticsFromList = (myRing, idxList, d, t, at, j, linez) -> (
    I := ideal(0_myRing);
    for Ln in linez do (
        I = trim(I + makeTripleSliceResultantQuarticsOnLine(myRing, idxList, d, t, at, j, Ln#0, Ln#1));
    );
    I
);

pairSliceResultantQuarticsFromList = (myRing, idxList, d, t, at, j, linez) -> (
    I := ideal(0_myRing);
    for Ln in linez do (
        I = trim(I + makePairSliceResultantQuarticsOnLine(myRing, idxList, d, t, at, j, Ln#0, Ln#1));
    );
    I
);

sliceResultantQuarticsFromList = (myRing, idxList, d, t, at, j, linez) -> (
    I := ideal(0_myRing);
    for Ln in linez do (
        I = trim(I + makeSliceResultantQuarticsOnLine(myRing, idxList, d, t, at, j, Ln#0, Ln#1));
    );
    I
);

