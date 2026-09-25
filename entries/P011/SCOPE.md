# P011 statement scope

This paper groups literature questions 13, 14 and 15. The current 762-line
Challenge exposes statements for all three and compiles on the target toolchain.
The completed proof verification is recorded below.

For question 13 the selected declarations are `MAFComposition.reactionEdit`,
`aggregate`, `directSum`, `parallel`, and `scalarNoncompositionality`. They retain
the input nonnegativity and attained-MAF hypotheses. The definitions expose
nonzero nonnegative flux feasibility, attained maximality, threshold-dependent
strict price cones, and the actual network operations. The scalar counterexample
includes the four explicit feasible-threshold predicates.

For question 15, `DegradationControl.sourceNetwork_arbitraryDegradationRegions`
uses nonnegative unary diluted reactions and a strongly connected source graph.
It gives the positive, zero and negative spectral-bound regions for arbitrary
nonnegative degradation. Its conclusion includes the actual complex-eigenvalue
definition of a real spectral bound. The additional
`partialActuation_stabilizable_iff_unactuatedCertificate` gives the general
Metzler actuator-placement criterion in positive-vector certificate form.
These statements concern the specified diluted model, not arbitrary nonlinear
reaction kinetics.

For question 14 the selected source endpoint is
`AutocatalyticCS.sourceDirectCSCoreEnum_exact`. Its hypotheses include complete
ordinary-core anchors, unique anchor matchings, exhaustive species/reaction
orders, and a checker carrying exact rational certificates. The checker must
give a dual certificate only for realising matchings with at least one species.
`certifiedAutocatalyticTest_nonempty` proves that such a checker exists for
every finite network, and `certifiedAutocatalyticTest_rejects_empty` proves
that every checker rejects the empty edge set.
`OneSpeciesExample.sourceDirectCSCoreEnum_example` proves the whole hypothesis
bundle for `A → 2A` and shows that the enumerator returns its one-edge core.
The Challenge
includes the bounded path search, disjoint path-pack generation, checked edge
table construction, ordinary-core semantics, and rational certificates used by
the exact enumerator. It preserves support containment versus matching-edge
containment rather than conflating these two orders.

Two graph-symmetry proofs needed the target Mathlib `Std.Symm` constructor.
The source-copy migration is recorded in
`preparation/graph-symmetry-migration.json`. Adjacency definitions are unchanged.
The matching-index helpers and the rest of the declaration boundary were included in the completed Comparator checks.

## Verification evidence

All eleven selected declarations passed Solution compilation, exact Comparator comparison and the con-ron, NanoDa and default Lean kernels on Lean 4.35.0-rc2. The local receipt covers commit `26cb2eccf42a33dd7b3e2de7665a9bae71dc7f82`; the [full cloud check](https://github.com/mmislan/palomar-p011-modular-autocatalytic-interfaces/actions/runs/36172946830) covers commit `7d987d4b9a017d63017e4b8ae7133da53f65ffd7`. This documentation correction preserves their proof, Challenge, Comparator and pinned dependency files byte-for-byte. These are completed mechanical checks; they do not constitute an independent human mathematical review.

[Claim-to-literature correspondence](CLAIM-EVIDENCE.md) records the source-reading assessment and the precise hypotheses of the selected results.
