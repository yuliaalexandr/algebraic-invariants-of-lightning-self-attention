# Algebraic Invariants of Lightning Self-Attention

This repository contains Macaulay2 code accompanying the paper on algebraic invariants of lightning self-attention.

The code is organized around two regimes:

- `t > 1`: the **cross-context** case
- `t = 1`: the **single-context** case

If you are new to the repository, start with one of the two driver scripts:

- `generateInvariants(t>1).m2`
- `generateInvariants(t=1).m2`

These are the main entry points. The other `.m2` files implement individual invariant families used by the driver scripts.

---

## Repository structure

### Main driver scripts

#### `generateInvariants(t>1).m2`
Driver for the cross-context case `t > 1`.

This script:
- fixes one output coordinate `(i,j)`
- builds the corresponding lightning self-attention output polynomial
- constructs the scaled coefficient ring
- generates the invariant families from the paper
- optionally compares the generated ideal with the implicit ideal in small examples

Use this file if you want to reproduce or test examples in the cross-context setting.

#### `generateInvariants(t=1).m2`
Driver for the single-context case `t = 1`.

This script generates the one-column invariant families separately, including:
- low-rank invariants
- Chow-type Lie flattening invariants

The `t=1` case is handled separately because the relevant invariant families differ from the `t>1` case.

---

## Helper files for the cross-context case (`t > 1`)

#### `linearRelations.m2`
Generates the linear relations among the scaled coefficient coordinates.

#### `crossColumnCubics.m2`
Generates the cubic cross-column relations.

#### `lowRankA.m2`
Generates invariants coming from the low-rank condition on the attention matrix.

#### `contextSyzygies.m2`
Generates the quartic context-syzygy invariants.

#### `veroneseInvariants.m2`
Generates the Veronese-type invariants from the paper, including:
- the basic catalecticant relations
- the cross-target relations
- the stronger block version

#### `quarticResultants.m2`
Generates quartic invariants from Sylvester resultants of restricted slice quadrics.

---

## Helper file for the single-context case (`t = 1`)

#### `singleContextInvariants.m2`
Generates the one-column invariant families used in the `t=1` case, including:
- low-rank minors
- Chow-type Lie flattening minors for the split `(2,1)` locus

---

## Quick start

## 1. Cross-context case: `t > 1`

Open Macaulay2 and run

```m2
load "generateInvariants(t>1).m2";
