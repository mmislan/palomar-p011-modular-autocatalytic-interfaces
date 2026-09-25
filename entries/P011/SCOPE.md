# P011 statement preparation

This paper groups literature questions 13, 14 and 15. The current 711-line
Challenge exposes statements for all three and compiles on the target toolchain.
Compilation establishes statement well-formedness, not proof verification or
final claim-to-literature fidelity.

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
orders, and a checker carrying exact rational certificates. The Challenge
includes the bounded path search, disjoint path-pack generation, checked edge
table construction, ordinary-core semantics, and rational certificates used by
the exact enumerator. It preserves support containment versus matching-edge
containment rather than conflating these two orders.

Two graph-symmetry proofs needed the target Mathlib `Std.Symm` constructor.
The source-copy migration is recorded in
`preparation/graph-symmetry-migration.json`. Adjacency definitions are unchanged.
The copied private matching-index helpers still require recursive Comparator
verification along with the rest of the declaration boundary.

Solution compilation, Comparator, independent kernels and literature fidelity
review remain pending for every selected statement.
