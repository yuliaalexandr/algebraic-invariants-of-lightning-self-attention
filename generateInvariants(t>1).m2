-- ============================================================
-- Driver script for algebraic invariants of lightning self-attention
-- in one fixed output coordinate (i,j), in the cross-context regime t > 1.
--
-- The user specifies:
--   * d          = embedding dimension
--   * at         = attention rank bound
--   * t          = sequence length
--   * targetRow  = output row i
--   * targetCol  = output column j
--
-- Assumptions:
--   * d' = 1
--   * t > 1
--
-- This script:
--   1. builds the polynomial output in the chosen coordinate (i,j),
--   2. constructs the scaled coefficient ring,
--   3. generates the invariant families from the paper,
--   4. optionally compares them with the implicit ideal in small examples.
--
-- The optional elimination block is only practical in very small cases.
-- The case t = 1 is treated separately.
-- ============================================================

restart

------------------------------------------------------------
-- User-chosen output coordinate (i,j)
------------------------------------------------------------

targetRow = 1;
targetCol = 1;

------------------------------------------------------------
-- User-chosen parameters
------------------------------------------------------------

d = 3;
at = 3;
t = 2;   -- requires t > 1
d' = 1;  -- fixed throughout

------------------------------------------------------------
-- Build the lightning self-attention output polynomial
-- and record its monomial/coefficient data in the chosen
-- output coordinate (targetRow, targetCol)
------------------------------------------------------------

R = QQ[a_(1,1)..a_(d,d), v_(1,1)..v_(d',d)];
A = transpose genericMatrix(R, a_(1,1), d, d);
V = transpose genericMatrix(R, v_(1,1), d, d');
S = R[x_(1,1)..x_(d,t)];
X = transpose genericMatrix(S, x_(1,1), t, d);
(monoms, coeffs) = coefficients((V * X * transpose(X) * A * X)_(targetRow - 1, targetCol - 1));

------------------------------------------------------------
-- Record monomial labels and scaled coefficient coordinates
------------------------------------------------------------

idxList = apply(flatten entries monoms, m ->
          toSequence sort flatten apply(#gens S, i ->
	  toList((exponents m)_0_i : (baseName (gens S)_i)#1)));

scaled = apply(flatten entries coeffs, c -> sub(c,R) / #(terms sub(c,R)));

------------------------------------------------------------
-- Optional: compute the implicit ideal of the parametrization
-- by elimination. This is only feasible in small examples.
------------------------------------------------------------

elimL = QQ[gens R, apply(idxList, idx -> y_idx), MonomialOrder => Eliminate(#gens R)];
gIdeal = ideal apply(#scaled, i ->
               sub(scaled_i, elimL) - (gens elimL)_(i + #gens R)) + minors(at+1, sub(A, elimL));
time J = eliminate(take(gens elimL, #gens R), gIdeal);
betti mingens J







------------------------------------------------------------
-- Ambient ring of formal coefficient coordinates
------------------------------------------------------------

L = QQ[apply(idxList, idx -> y_idx)];

------------------------------------------------------------
-- Linear relations
------------------------------------------------------------

load "linearRelations.m2";
linear = ideal makeLinearRelations(L, idxList, d, t, targetCol);
betti mingens linear

------------------------------------------------------------
-- Low-rank relations coming from rank(A) <= at
------------------------------------------------------------

load "lowRankA.m2";
lowRank = ideal makeLowRankA(L, d, t, at, targetCol);
betti mingens lowRank

------------------------------------------------------------
-- Cross-column cubic relations
------------------------------------------------------------

load "crossColumnCubics.m2";
cubicRels = ideal makeCrossColumnCubics(L, d, t, targetCol);
betti mingens cubicRels

------------------------------------------------------------
-- Context-syzygy relations
------------------------------------------------------------

load "contextSyzygies.m2";
contextSyz = ideal makeContextSyzygies(L, idxList, d, t, targetCol);
betti mingens contextSyz

------------------------------------------------------------
-- Veronese-type invariants
-- Here r = 2 is the quartic case. For other admissible r,
-- use the same helper with the desired value of r.
------------------------------------------------------------

load "veroneseInvariants.m2";
veronese2 = ideal (makeVeroneseInvariants(L, idxList, d, t, at, targetCol, 2))#"all";
betti mingens veronese2

------------------------------------------------------------
-- Resultant quartics from restrictions to chosen lines
-- The list linez is user-supplied.
-- This code may be very slow.
------------------------------------------------------------

load "quarticResultants.m2";

linez = {
    {{2,2,1},{2,2,-1}},
    {{2,2,1},{2,1,2}},
    {{2,2,1},{2,1,1}},
    {{2,2,1},{2,1,0}},
    {{2,2,1},{2,1,-1}},
    {{2,2,-1},{2,1,2}},
    {{2,2,-1},{2,1,1}},
    {{2,2,-1},{2,1,0}},
    {{2,2,-1},{2,1,-1}},
    {{2,1,2},{2,1,1}},
    {{2,1,2},{2,0,1}},
    {{2,1,2},{2,0,-1}}
};


qRes    = sliceResultantQuarticsFromList(L, idxList, d, t, at, targetCol, linez);
betti mingens qRes

------------------------------------------------------------
-- Create a candidate implicit ideal
------------------------------------------------------------

myJ = linear + lowRank + cubicRels + contextSyz + veronese2 + qRes;
betti mingens myJ



-- Optional: sanity check + completeness
-- Only works if J can be computed via elimination

isSubset(myJ, sub(J, L))
myJ == sub(J, L)
