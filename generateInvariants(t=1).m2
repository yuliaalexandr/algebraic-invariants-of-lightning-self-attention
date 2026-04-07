-- ============================================================
-- Driver script for t = 1 invariants in one fixed output row.
--
-- User specifies:
--   * d   = embedding dimension
--   * at  = attention rank bound
--
-- Assumptions:
--   * t = 1
--   * d' = 1
--
-- This script:
--   1. builds the single-context output cubic,
--   2. constructs the scaled coefficient ring,
--   3. generates low-rank and Chow-type invariants separately,
--   4. optionally compares them with the implicit ideal.
-- ============================================================

restart

------------------------------------------------------------
-- User-chosen parameters
------------------------------------------------------------

d = 3;
at = 3;
t = 1;
d' = 1;
targetRow = 1;

------------------------------------------------------------
-- Build the single-context output polynomial
------------------------------------------------------------

R = QQ[a_(1,1)..a_(d,d), v_(1)..v_(d)];
A = transpose genericMatrix(R, a_(1,1), d, d);
V = transpose genericMatrix(R, v_(1), d, 1);

S = R[x_(1)..x_(d)];
X = transpose genericMatrix(S, x_(1), 1, d);

(monoms, coeffs) = coefficients((V * X * transpose(X) * A * X)_(targetRow - 1, 0));

------------------------------------------------------------
-- Record monomial labels and scaled coefficient coordinates
------------------------------------------------------------

idxList = apply(flatten entries monoms, m ->
    flatten apply(0..(#gens S - 1), r -> toList((exponents m)_0_r : (r+1)))
);

scaled = apply(flatten entries coeffs, c -> sub(c, R) / #(terms sub(c, R)));

------------------------------------------------------------
-- Optional: compute the implicit ideal by elimination
-- Only practical in very small examples.
------------------------------------------------------------

elimL = QQ[gens R, apply(idxList, idx -> y_(toString idx)), MonomialOrder => Eliminate(#gens R)];
gIdeal = ideal apply(#scaled, i ->
    sub(scaled_i, elimL) - (gens elimL)_(i + #gens R)
);

time J = eliminate(take(gens elimL, #gens R), gIdeal);
betti mingens J

------------------------------------------------------------
-- Ambient ring of formal coefficient coordinates
------------------------------------------------------------

L = QQ[apply(idxList, idx -> y_(toString idx))];

------------------------------------------------------------
-- Generate t = 1 invariants
------------------------------------------------------------

load "singleContextInvariants.m2";

-- Low-rank family
Nmat    = makeSingleContextLowRankMatrix(L, idxList, d);
lowRank = makeSingleContextLowRankIdeal(L, idxList, d, at);

-- Chow-type Lie flattening family
MLie   = makeSingleContextLieMatrix(L, idxList, d);
chow21 = makeSingleContextLieIdeal(L, idxList, d);

-- Combined ideal
allI = trim(lowRank + chow21);

------------------------------------------------------------
-- Inspect generators
------------------------------------------------------------

betti mingens lowRank
betti mingens chow21
betti mingens allI

------------------------------------------------------------
-- Optional comparisons with the implicit ideal
------------------------------------------------------------

isSubset(lowRank, sub(J, L))
isSubset(chow21, sub(J, L))
isSubset(allI, sub(J, L))

allI == sub(J, L)
