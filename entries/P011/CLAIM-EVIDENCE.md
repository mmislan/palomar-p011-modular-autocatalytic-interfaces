# P011: claim-to-evidence correspondence

Source-reading review dated 2026-09-24. No Lean was executed for this review.

P011 selects eleven declarations for literature problems 13, 14 and 15 from
[Registry/P011/Challenge.lean](../../Registry/P011/Challenge.lean). The three
namespace groups in that one file are independent: none uses a definition from
another. The `AutocatalyticCS` group and the universe-polymorphic column
calculus of the `MAFComposition` group are split into scoped blocks that mirror
their source modules, so that their definitions elaborate to the same terms as
the Solution's
(see the Comparator alignment in
[P011-TARGET-API-MIGRATION.json](../../preparation/P011-TARGET-API-MIGRATION.json)).
The older alternative configuration P011A predates this alignment.
**Problem 15 fixed-point dependency replaced (2026-09-24).** The Solution path
previously reached `External.SchauderFixedPoint`, a third-party source with an
unresolved license. Its only use was `positiveMatrix_exists_normalizedPositive_eigenvector`
in `PerronExistence.lean`. That lemma's statement is unchanged. It is now proved by the
independent Collatz–Wielandt argument in
[PositivePerron.lean](../../proofs/DegradationControl/PositivePerron.lean). The static import
closure no longer contains `DegradationControl/External/`. See
[P011-PERRON-REPLACEMENT.json](../../preparation/P011-PERRON-REPLACEMENT.json).

**Certified checker revised (2026-09-25).** In the earlier submission, the
`negative` field of `CertifiedAutocatalyticTest` demanded a
`NegativeRationalCertificate` for every matching realising a rejected edge set,
including the empty matching. Such a certificate needs a positive coordinate,
which is impossible on an empty index set. That made the checker type
uninhabited and the enumeration theorem vacuous. The field now asks for a dual
certificate only for realising matchings with at least one species; a matching
with no species is never autocatalytic, so it needs none. Three selected
declarations now show that the revised theorem applies:
`certifiedAutocatalyticTest_nonempty` (a checker exists for every finite
network), `certifiedAutocatalyticTest_rejects_empty` (every checker rejects the
empty edge set) and `OneSpeciesExample.sourceDirectCSCoreEnum_example` (an
explicit instance). Checker existence rests on an exact rational Gordan
alternative, proved by Fourier–Motzkin elimination over `ℚ` in
[RationalGordan.lean](../../proofs/AutocatalyticCS/RationalGordan.lean). The
elimination never passes through the reals, so no density argument is used for
the weak dual inequalities. The checker is defined classically; it is an
existence result, not an executable rational solver. Anchor completeness and
anchor uniqueness remain hypotheses of the general theorem. See
[P011-CHECKER-REPAIR.json](../../preparation/P011-CHECKER-REPAIR.json).

## Selected declarations

| Declaration | Exact formal content (Challenge) | Informal claim | Manuscript | Evidence |
|---|---|---|---|---|
| `MAFComposition.reactionEdit` | For `N` with `N.InputNonnegative`, `VectorNonnegative a`, `N.IsMAF α` and `(N.addReaction a b).IsMAF β`: `α < β ↔ ¬ ∀ q, α < q → ∃ p, p ∈ N.priceCone q ∩ reactionHalfspace a b q`. | One added reaction strictly raises the attained MAF iff, at some threshold above it, no old strict price is strict for the new column. | Thm 3.5(i) | Module-level historical receipt only (below). |
| `MAFComposition.aggregate` | For `C` with `Matrix.EntrywiseNonnegative C`, nonnegative input, `N.IsMAF a` and `(N.aggregate C).IsMAF b`: `a < b ↔ ¬ ∀ q, a < q → ∃ p, (∀ z, 0 ≤ p z) ∧ Matrix.vecMul p C ∈ N.priceCone q`. | Aggregation strictly raises the MAF iff, at some threshold above it, no aggregate price lifts. | Thm 3.5(ii) | Module-level historical receipt only. |
| `MAFComposition.directSum` | For nonnegative inputs, `N₁.IsMAF a` and `N₂.IsMAF b` imply `(N₁.directSum N₂).IsMAF (max a b)`. | Disjoint union takes the maximum. | Thm 3.5(iii) | Module-level historical receipt only. |
| `MAFComposition.parallel` | For shared species, nonnegative inputs and `IsMAF` values `a`, `b` and `c` of `N₁`, `N₂` and `N₁.parallel N₂`: `max a b < c ↔ ¬ ∀ q, max a b < q → ∃ p, p ∈ N₁.priceCone q ∩ N₂.priceCone q`. | Strict synergy iff, at some threshold above both MAFs, no common strict price exists. | Thm 3.5(iv) | Module-level historical receipt only. |
| `MAFComposition.scalarNoncompositionality` | `ExactThreshold N1Feasible 2 ∧ ExactThreshold N2Feasible 2 ∧ ExactThreshold N1N1Feasible 2 ∧ ExactThreshold N2N1Feasible 4`, with explicit two-inequality feasibility predicates. | Equal component MAFs can yield different composite MAFs. | Thm 3.8 | Module-level historical receipt only. |
| `DegradationControl.sourceNetwork_arbitraryDegradationRegions` | Let `ι` be finite, decidable and nonempty. Assume `rs` is a list of unary reactions, each with `NonnegativeReaction`, and `SourceIrreducible rs`. Then for every `d`: (1) `d ≥ 0` and a positive real spectral bound of `reactionPart rs - diag d` iff `d ≥ 0` and `∃ v ≫ 0, d < projectiveDegradation … v` componentwise. (2) `IrreduciblePhysicalSpectralState … d 0` iff `∃` normalized `v ≫ 0` with nonnegative projective degradation equal to `d`. (3) The negative case mirrors (1) with `projectiveDegradation … v < d`. `IsRealSpectralBound` means a real eigenvalue of the complexified matrix that dominates every complex eigenvalue's real part. | Growth, criticality and extinction regions for arbitrary nonnegative species-specific degradation in the strongly connected diluted source model. | Thm 5.4 (three sign cases; the general-λ form is not selected) | Historical axiom audit `preparation/historical-audits/P011.json`: standard axioms only. |
| `DegradationControl.partialActuation_stabilizable_iff_unactuatedCertificate` | For finite decidable `U` and `S`, a Metzler `A` on `U ⊕ S` satisfies `PartiallyStabilizable A ↔ ExtinctionCertificate (unactuatedBlock A)`. `PartiallyStabilizable A` means some `d ≥ 0` vanishing on `U` gives `A - diag d` a positive vector `v` with `(A - diag d) v ≪ 0`. | Degradation on `S` can yield a strict extinction certificate iff the unactuated block already has one. | Thm 5.5, certificate form (spectral form not selected) | No per-declaration historical record found in this repository. |
| `AutocatalyticCS.sourceDirectCSCoreEnum_exact` | Assume anchor completeness for `OrdinaryCore Q`, `IsUniqueMatching` for every anchor subgraph, exhaustive species and reaction lists, and a `CertifiedAutocatalyticTest Q`. Then `edges ∈ sourceDirectCSCoreEnum … ↔ IsCore (AutocatalyticEdgeSet Q) edges`. A checker's `true` answers carry a rational primal certificate for some realising matching; its `false` answers carry a rational dual certificate for every realising matching `E` with `E.species.Nonempty`. | Exact enumeration of child-selection cores from uniquely matched ordinary-core anchors. | Thm 4.7 with Construction 4.6 | Historical axiom audit `preparation/historical-audits/P011.json` (earlier checker form): standard axioms only. |
| `AutocatalyticCS.certifiedAutocatalyticTest_nonempty` | For every finite `X`, `R` with decidable equality and every `Q : ReactionNetwork X R`: `Nonempty (CertifiedAutocatalyticTest Q)`. | Certified checkers exist for every finite network, so the enumeration theorem is not vacuous. | Prop 4.8 | Proved via `IndexedMatching.certificate_alternative` and the rational Gordan alternative. |
| `AutocatalyticCS.certifiedAutocatalyticTest_rejects_empty` | Every `checker : CertifiedAutocatalyticTest Q` has `checker.test ∅ = false`. | The empty edge set is rejected, without any dual certificate. | Prop 4.8 | Proved from `not_autocatalyticEdgeSet_empty`. |
| `AutocatalyticCS.OneSpeciesExample.sourceDirectCSCoreEnum_example` | For `network` (`A → 2A`: reactant 1, product 2 on `Unit × Unit`) and its one-edge `anchor`: the singleton orders are exhaustive, `[anchor]` is complete for `OrdinaryCore network`, the anchor subgraph is a unique matching, `Nonempty (CertifiedAutocatalyticTest network)`, `IsCore (AutocatalyticEdgeSet network) {((), ())}`, and for every checker `sourceDirectCSCoreEnum network [anchor] [()] [()] checker = {{((), ())}}`. | A nonempty network satisfies the whole hypothesis bundle and the enumerator returns its core. | Example 4.9 | Proved in `proofs/AutocatalyticCS/OneSpeciesExample.lean`. |

Historical records predate current sources. The MAF receipt extract
(`migration/historical-receipts/9d5f7adc8fb9aa6b098a.json`) lists three
dependency mismatches. `proofs/MAFComposition/Gordan.lean` and
`proofs/AutocatalyticCS/SourceGraphBridge.lean` differ from the audit hashes
because of the recorded compatibility migrations.

## Literature correspondence

- Problem 13: Gagrani, Wang, De Decker and Lacoste, arXiv:2603.02627
  (doi:10.48550/arXiv.2603.02627). The companion manuscript reports that this
  work names composition rules for the MAF as an open direction. The entry
  gives an exact price-profile calculus for attained MAFs and nonnegative
  inputs, and it proves that no scalar rule exists.
- Problem 14: Golnik, Gatter, Stadler and Vassena, arXiv:2603.02770
  (doi:10.48550/arXiv.2603.02770), Definition 3.4. The entry gives a
  conditional exact reconstruction of child-selection cores from a complete
  list of uniquely matched ordinary-core anchors.
- Problem 15: Nandan, Nghe and Unterberger, *Autocatalytic cores in the diluted
  regime: classification and properties*, J. Math. Biol. 92 (2026) 36
  (doi:10.1007/s00285-026-02357-7; arXiv:2507.15546). This builds on
  Unterberger and Nghe (2022). The entry characterizes growth, criticality and
  extinction for arbitrary nonnegative degradation in the finite strongly
  connected diluted source model only. It is not a theorem about arbitrary
  nonlinear networks.

This is agent-assisted source reading, not an independent human review.

## Evidence boundary

- Replacement proof: `PositivePerron.lean` replaces the third-party
  fixed-point file. The downstream degradation statements are unchanged.
- Target API migration: deprecated Mathlib names, simp normal-form changes and
  one style lint were repaired in ten proof files, and two AutocatalyticCS
  files were adjusted for the Comparator alignment
  ([record](../../preparation/P011-TARGET-API-MIGRATION.json)). The whole
  Solution closure builds on Lean 4.35.0-rc2 with the pinned Mathlib and
  warnings as errors. No selected statement changed.
- Not selected: the pointwise price-cone identities, Prop 3.6, Thm 3.9, the
  general-λ and spectral actuation forms of Thms 5.4 and 5.5, and the
  hand-proved extensions of Remark 5.8.
- Conditional premises: attained MAFs and nonnegative inputs; anchor
  completeness and uniqueness; certified checker; rational semipositivity;
  nonnegative unary reactions with an irreducible source; Metzler matrices.
- Earlier snapshot (eight declarations, original checker form): the local
  official verifier passed on Lean 4.35.0-rc2 ([receipt](../../preparation/verification/P011-release-candidate-run/result.json)). That receipt is
  historical. It does not cover the revised checker or the three new
  declarations.
- Local official verifier on Lean 4.35.0-rc2 (2026-09-25), commit `26cb2ec`
  of this revision: PASS for all eleven selected declarations. The run covered
  the Solution build, exact Comparator comparison, the permitted axioms only,
  and the con-ron, nanoda and default Lean kernels ([receipt](../../preparation/verification/P011-checker-repair-run/result.json)). The
  receipt's source snapshot matches every file of that commit. The subsequent full cloud check is recorded below.

## Published-commit verification

All eleven selected declarations passed Solution compilation, exact Comparator comparison and the con-ron, NanoDa and default Lean kernels on Lean 4.35.0-rc2. The local receipt covers commit `26cb2eccf42a33dd7b3e2de7665a9bae71dc7f82`; the [full cloud check](https://github.com/mmislan/palomar-p011-modular-autocatalytic-interfaces/actions/runs/36172946830) covers commit `7d987d4b9a017d63017e4b8ae7133da53f65ffd7`. This documentation correction preserves their proof, Challenge, Comparator and pinned dependency files byte-for-byte. These are completed mechanical checks; they do not constitute an independent human mathematical review.
