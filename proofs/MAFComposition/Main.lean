import proofs.MAFComposition.Core
import proofs.MAFComposition.DualCalculus
import proofs.MAFComposition.Gordan
import proofs.MAFComposition.Threshold
import proofs.MAFComposition.Composition
import proofs.MAFComposition.Aggregation
import proofs.MAFComposition.Attainment
import proofs.MAFComposition.DirectSum
import proofs.MAFComposition.ReactionEdit
import proofs.MAFComposition.Simulation
import proofs.MAFComposition.Transition

/-!
Umbrella import for the verified MAF composition and reaction-edit calculus.
Every dependency is compiled with warnings treated as errors by
`scripts/verify_proof.py`.
-/

namespace MAFComposition

variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- Named root interface: the strict finite alternative from which the MAF
threshold, edit, aggregation, and coupling calculus is derived. -/
theorem mafCompositionCalculusKernel (C : Matrix ι κ ℝ) :
    PrimalNonnegative C ↔ ¬ StrictColumnDual C :=
  primal_iff_not_strictColumnDual C

/-- Research interface for exact one-reaction strict increase. -/
theorem reactionEdit
    (N : Network ι κ) (hN : N.InputNonnegative)
    (a b : ι → ℝ) (ha0 : VectorNonnegative a)
    {α β : ℝ} (hα : N.IsMAF α) (hβ : (N.addReaction a b).IsMAF β) :
    α < β ↔
      ¬ ∀ q, α < q → ∃ p, p ∈ N.priceCone q ∩ reactionHalfspace a b q :=
  addReaction_strictIncrease_iff_no_pricesAbove N hN a b ha0 hα hβ

/-- Research interface for aggregation strict increase through lifted prices. -/
theorem aggregate
    {ζ : Type} [Fintype ζ]
    (C : Matrix ζ ι ℝ) (hC : Matrix.EntrywiseNonnegative C)
    (N : Network ι κ) (hN : N.InputNonnegative)
    {a b : ℝ} (ha : N.IsMAF a) (hb : (N.aggregate C).IsMAF b) :
    a < b ↔
      ¬ ∀ q, a < q → ∃ p : ζ → ℝ,
        (∀ z, 0 ≤ p z) ∧ Matrix.vecMul p C ∈ N.priceCone q :=
  aggregate_strictIncrease_iff_no_liftedPricesAbove C hC N hN ha hb

/-- Research interface for the block-diagonal maximum law. -/
theorem directSum
    {ζ ρ : Type} [Fintype ζ] [Fintype ρ]
    (N₁ : Network ι κ) (N₂ : Network ζ ρ)
    (hA₁ : N₁.InputNonnegative) (hA₂ : N₂.InputNonnegative)
    {a b : ℝ} (ha : N₁.IsMAF a) (hb : N₂.IsMAF b) :
    (N₁.directSum N₂).IsMAF (max a b) :=
  directSum_isMAF_max N₁ N₂ hA₁ hA₂ ha hb

/-- Research interface for exact shared-species strict synergy. -/
theorem parallel
    {ρ : Type} [Fintype ρ]
    (N₁ : Network ι κ) (N₂ : Network ι ρ)
    (hA₁ : N₁.InputNonnegative) (hA₂ : N₂.InputNonnegative)
    {a b c : ℝ} (ha : N₁.IsMAF a) (hb : N₂.IsMAF b)
    (hc : (N₁.parallel N₂).IsMAF c) :
    max a b < c ↔
      ¬ ∀ q, max a b < q → ∃ p, p ∈ N₁.priceCone q ∩ N₂.priceCone q :=
  parallel_strictSynergy_iff_no_commonPricesAbove N₁ N₂ hA₁ hA₂ ha hb hc

/-- Research interface disproving scalar-only parallel compositionality. -/
theorem scalarNoncompositionality :
    ExactThreshold N1Feasible 2 ∧ ExactThreshold N2Feasible 2 ∧
      ExactThreshold N1N1Feasible 2 ∧ ExactThreshold N2N1Feasible 4 :=
  scalar_parallel_composition_impossible

/-- Research interface for strict all-species productivity, kept distinct from
the non-strict MAF threshold alternative. -/
theorem strictProductivityAlternative
    [Nonempty ι] (C : Matrix ι κ ℝ) :
    StrictProductive C ↔ ¬ WeakColumnDual C :=
  strictProductive_iff_not_weakColumnDual C

omit [Fintype ι] in
/-- Source-domain attainment interface: for a finite nonempty reaction family,
an explicit nonnegative upper bound on every feasible threshold turns the MAF
supremum into an attained maximum. -/
theorem sourceDomainAttainment
    [Nonempty κ] (N : Network ι κ) (hB : N.OutputNonnegative)
    {U : ℝ} (hU : 0 ≤ U) (hbound : N.ThresholdBoundedAbove U) :
    ∃ a, N.IsMAF a :=
  exists_isMAF_of_bounded N hB hU hbound

/-- Chemical source-domain corollary eliminating the abstract boundedness
premise via a uniform reaction-column stoichiometric bound. -/
theorem chemicalSourceDomainAttainment
    [Nonempty κ] (N : Network ι κ) (hB : N.OutputNonnegative)
    {U : ℝ} (hU : 0 ≤ U)
    (hinput : ∀ r, 0 < ∑ i, N.input i r)
    (hcolumn : ∀ r, (∑ i, N.output i r) ≤ U * ∑ i, N.input i r) :
    ∃ a, N.IsMAF a :=
  exists_isMAF_of_columnBound N hB hU hinput hcolumn

end MAFComposition
