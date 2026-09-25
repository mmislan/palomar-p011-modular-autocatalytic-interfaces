import proofs.AutocatalyticCS.SourceCandidateCompleteness
import proofs.AutocatalyticCS.ExactSemipositivity
import proofs.AutocatalyticCS.RationalGordan

/-!
Proof-carrying exact autocatalytic recognition and minimal direct extraction.
The checker receives rational primal/dual certificates, never a proof that an
edge set is already a CS core.
-/

namespace AutocatalyticCS

variable {X R : Type*} [Fintype X] [Fintype R]
variable [DecidableEq X] [DecidableEq R]
variable {Q : ReactionNetwork X R}

def IndexedMatching.rationalMatrix (E : IndexedMatching Q) :
    Matrix E.species E.species ℚ :=
  fun i j => (Q.net i.1 (E.assign j).1 : ℚ)

structure PositiveRationalCertificate (E : IndexedMatching Q) where
  vector : E.species → ℚ
  nonnegative : ∀ i, 0 ≤ vector i
  nonzero : vector ≠ 0
  verifies : ∀ i, 0 < E.rationalMatrix.mulVec vector i

structure NegativeRationalCertificate (E : IndexedMatching Q) where
  vector : E.species → ℚ
  nonnegative : ∀ i, 0 ≤ vector i
  positive : ∃ i, 0 < vector i
  verifies : ∀ j, ∑ i, E.rationalMatrix i j * vector i ≤ 0

omit [Fintype X] [Fintype R] in
theorem PositiveRationalCertificate.autocatalytic
    {E : IndexedMatching Q} (c : PositiveRationalCertificate E) :
    E.toChildSelection.Autocatalytic := by
  rw [IndexedMatching.toChildSelection_autocatalytic_iff]
  exact ⟨c.vector, c.nonnegative, c.nonzero, c.verifies⟩

omit [Fintype X] [Fintype R] in
theorem NegativeRationalCertificate.not_autocatalytic
    {E : IndexedMatching Q} (c : NegativeRationalCertificate E) :
    ¬ E.toChildSelection.Autocatalytic := by
  rw [IndexedMatching.toChildSelection_autocatalytic_iff]
  rintro ⟨v, hvnonneg, -, hvpos⟩
  let lhs : ℚ := ∑ i, c.vector i *
    (∑ j, E.rationalMatrix i j * v j)
  have hlhs : 0 < lhs := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (c.nonnegative i) (hvpos i).le
    · rcases c.positive with ⟨i, hi⟩
      exact ⟨i, Finset.mem_univ _, mul_pos hi (hvpos i)⟩
  have hrearrange : lhs = ∑ j, v j *
      (∑ i, E.rationalMatrix i j * c.vector i) := by
    simp only [lhs, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrhs : (∑ j, v j *
      (∑ i, E.rationalMatrix i j * c.vector i)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    exact mul_nonpos_of_nonneg_of_nonpos (hvnonneg j) (c.verifies j)
  rw [hrearrange] at hlhs
  exact (not_lt_of_ge hrhs) hlhs

/-! ### The empty matching and other boundary cases -/

omit [Fintype X] [Fintype R] in
/-- An autocatalytic matching has a species: its semipositivity vector is
nonzero, and every vector on an empty index set is zero. -/
theorem IndexedMatching.species_nonempty_of_autocatalytic
    (E : IndexedMatching Q) (h : E.toChildSelection.Autocatalytic) :
    E.species.Nonempty := by
  rw [← Finset.card_pos, E.species_card]
  exact E.card_pos_of_autocatalytic h

omit [Fintype X] [Fintype R] in
/-- No matching with an empty species set is autocatalytic. -/
theorem IndexedMatching.not_autocatalytic_of_species_eq_empty
    (E : IndexedMatching Q) (h : E.species = ∅) :
    ¬ E.toChildSelection.Autocatalytic := fun hauto => by
  have := E.species_nonempty_of_autocatalytic hauto
  rw [h] at this
  exact Finset.not_nonempty_empty this

omit [Fintype X] [Fintype R] in
/-- A rational primal certificate forces a nonempty species set. -/
theorem PositiveRationalCertificate.species_nonempty
    {E : IndexedMatching Q} (c : PositiveRationalCertificate E) :
    E.species.Nonempty :=
  E.species_nonempty_of_autocatalytic c.autocatalytic

omit [Fintype X] [Fintype R] in
/-- Every representation of the empty edge set is the empty matching. -/
theorem IndexedMatching.species_eq_empty_of_edgeFinset_eq_empty
    (E : IndexedMatching Q) (h : E.edgeFinset = ∅) : E.species = ∅ := by
  rw [← Finset.card_eq_zero, E.species_card, ← E.edgeFinset_card, h,
    Finset.card_empty]

omit [Fintype X] [Fintype R] in
/-- The empty edge set is not autocatalytic. -/
theorem not_autocatalyticEdgeSet_empty : ¬ AutocatalyticEdgeSet Q ∅ := by
  rintro ⟨E, hE, hauto⟩
  exact E.not_autocatalytic_of_species_eq_empty
    (E.species_eq_empty_of_edgeFinset_eq_empty hE) hauto

/-- A concrete exact-recognition boundary.  A `true` answer carries a rational
primal witness for a matching with these edges.  A `false` answer carries a
rational Gordan--Stiemke obstruction for every nonempty representation of those edges.
Empty matchings are non-autocatalytic because their vectors are all zero.
All fields are checked by Lean using exact rational arithmetic. -/
structure CertifiedAutocatalyticTest (Q : ReactionNetwork X R) where
  test : Finset (X × R) → Bool
  positive : ∀ edges, test edges = true →
    ∃ E : IndexedMatching Q, E.edgeFinset = edges ∧
      Nonempty (PositiveRationalCertificate E)
  negative : ∀ edges, test edges = false →
    ∀ E : IndexedMatching Q, E.edgeFinset = edges →
      E.species.Nonempty → NegativeRationalCertificate E

omit [Fintype X] [Fintype R] in
theorem CertifiedAutocatalyticTest.exact
    (checker : CertifiedAutocatalyticTest Q) (edges : Finset (X × R)) :
    checker.test edges = true ↔ AutocatalyticEdgeSet Q edges := by
  constructor
  · intro h
    rcases checker.positive edges h with ⟨E, hE, ⟨c⟩⟩
    exact ⟨E, hE, c.autocatalytic⟩
  · rintro ⟨E, hE, hauto⟩
    by_contra hnot
    have hfalse : checker.test edges = false := Bool.eq_false_of_not_eq_true hnot
    exact (checker.negative edges hfalse E hE
      (E.species_nonempty_of_autocatalytic hauto)).not_autocatalytic hauto

omit [Fintype X] [Fintype R] in
/-- Every checker rejects the empty edge set, without any dual certificate. -/
theorem certifiedAutocatalyticTest_rejects_empty
    (checker : CertifiedAutocatalyticTest Q) : checker.test ∅ = false := by
  cases h : checker.test ∅
  · rfl
  · exact absurd ((checker.exact ∅).1 h) not_autocatalyticEdgeSet_empty

omit [Fintype X] [Fintype R] in
/-- Only edge sets of actual matchings can pass a checker; malformed or
non-matching edge sets are rejected. -/
theorem CertifiedAutocatalyticTest.exists_matching_of_test
    (checker : CertifiedAutocatalyticTest Q) {edges : Finset (X × R)}
    (h : checker.test edges = true) :
    ∃ E : IndexedMatching Q, E.edgeFinset = edges := by
  obtain ⟨E, hE, -⟩ := checker.positive edges h
  exact ⟨E, hE⟩

/-! ### Certificate completeness and existence of a checker -/

omit [Fintype X] [Fintype R] in
/-- **Rational certificate alternative.** For a matching with at least one
species, either a rational primal certificate or a rational dual
(Gordan--Stiemke) certificate exists. This is Ville's form of Gordan's theorem,
derived from the exact rational Gordan alternative for the stacked system
`[A; I] x > 0`. -/
theorem IndexedMatching.certificate_alternative (E : IndexedMatching Q)
    (hne : E.species.Nonempty) :
    Nonempty (PositiveRationalCertificate E) ∨
      Nonempty (NegativeRationalCertificate E) := by
  classical
  let A := E.rationalMatrix
  let M : E.species ⊕ E.species → E.species → ℚ :=
    Sum.elim (fun i j => A i j) (fun k j => if k = j then 1 else 0)
  obtain ⟨k₀, hk₀⟩ := hne
  by_cases hfeas : ∃ x : E.species → ℚ, ∀ r, 0 < ∑ j, M r j * x j
  · obtain ⟨x, hx⟩ := hfeas
    have hxpos : ∀ k, 0 < x k := fun k => by
      simpa [M] using hx (Sum.inr k)
    refine Or.inl ⟨⟨x, fun k => (hxpos k).le, fun h0 => ?_, fun i => ?_⟩⟩
    · have := hxpos ⟨k₀, hk₀⟩
      rw [h0] at this
      exact lt_irrefl 0 this
    · simpa [M, A, Matrix.mulVec, dotProduct] using hx (Sum.inl i)
  · obtain ⟨y, hy_nonneg, ⟨r₀, hr₀⟩, hy⟩ := RationalGordan.gordan M hfeas
    let u : E.species → ℚ := fun i => y (Sum.inl i)
    have hcol : ∀ j, ∑ i, E.rationalMatrix i j * u i = -y (Sum.inr j) := by
      intro j
      have := hy j
      rw [Fintype.sum_sum_type] at this
      simp only [M, Sum.elim_inl, Sum.elim_inr, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
      have hcomm : ∑ i, E.rationalMatrix i j * u i = ∑ i, y (Sum.inl i) * A i j :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [hcomm]
      linarith
    refine Or.inr ⟨⟨u, fun i => hy_nonneg _, ?_, fun j => ?_⟩⟩
    · rcases r₀ with i | k
      · exact ⟨i, hr₀⟩
      · by_contra hnone
        push Not at hnone
        have hu0 : ∀ i, u i = 0 := fun i => le_antisymm (hnone i) (hy_nonneg _)
        have := hcol k
        simp only [hu0, mul_zero, Finset.sum_const_zero] at this
        linarith
    · rw [hcol j]
      linarith [hy_nonneg (Sum.inr j)]

/-- A checker that exists for every finite reaction network. It answers `true`
exactly on autocatalytic edge sets; its positive certificates are the
semipositivity witnesses, and its negative certificates come from the rational
certificate alternative. It is defined classically and is not claimed to be
an executable rational solver. -/
noncomputable def canonicalCertifiedTest (Q : ReactionNetwork X R) :
    CertifiedAutocatalyticTest Q where
  test edges := @decide (AutocatalyticEdgeSet Q edges) (Classical.propDecidable _)
  positive edges h := by
    obtain ⟨E, hE, hauto⟩ := @of_decide_eq_true _ (Classical.propDecidable _) h
    rw [IndexedMatching.toChildSelection_autocatalytic_iff] at hauto
    obtain ⟨v, hv_nonneg, hv_ne, hv_pos⟩ := hauto
    exact ⟨E, hE, ⟨⟨v, hv_nonneg, hv_ne, hv_pos⟩⟩⟩
  negative edges h E hE hne := by
    have hnot : ¬ AutocatalyticEdgeSet Q edges :=
      @of_decide_eq_false _ (Classical.propDecidable _) h
    refine Classical.choice ?_
    rcases E.certificate_alternative hne with hpos | hneg
    · obtain ⟨c⟩ := hpos
      exact absurd ⟨E, hE, c.autocatalytic⟩ hnot
    · exact hneg

omit [Fintype X] [Fintype R] in
/-- **Existence of a certified checker.** Every finite reaction network admits a
`CertifiedAutocatalyticTest`, so the enumeration theorems below have instances
for every network. -/
theorem certifiedAutocatalyticTest_nonempty (Q : ReactionNetwork X R) :
    Nonempty (CertifiedAutocatalyticTest Q) :=
  ⟨canonicalCertifiedTest Q⟩

/-- Extensional direct candidates retained exactly when they are
autocatalytic and no smaller direct candidate is autocatalytic.  This is the
batch normal form of the increasing-cardinality antichain update. -/
def certifiedDirectCSCoreEnum (candidates : Finset (Finset (X × R)))
    (checker : CertifiedAutocatalyticTest Q) : Finset (Finset (X × R)) :=
  candidates.filter fun edges =>
    checker.test edges && decide (∀ smaller ∈ candidates,
      smaller < edges → checker.test smaller = false)

theorem mem_certifiedDirectCSCoreEnum_iff
    (candidates : Finset (Finset (X × R)))
    (checker : CertifiedAutocatalyticTest Q)
    (complete : ∀ edges, AutocatalyticEdgeSet Q edges → edges ∈ candidates)
    (edges : Finset (X × R)) :
    edges ∈ certifiedDirectCSCoreEnum candidates checker ↔
      IsCore (AutocatalyticEdgeSet Q) edges := by
  rw [certifiedDirectCSCoreEnum, Finset.mem_filter]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨-, htest, hsmaller⟩
    refine ⟨(checker.exact edges).1 htest, ?_⟩
    intro smaller hlt hauto
    have hfalse := hsmaller smaller (complete smaller hauto) hlt
    have htrue := (checker.exact smaller).2 hauto
    rw [hfalse] at htrue
    exact Bool.false_ne_true htrue
  · rintro hcore
    have hmem := complete edges hcore.1
    have htest : checker.test edges = true := (checker.exact edges).2 hcore.1
    refine ⟨hmem, htest, ?_⟩
    intro smaller _ hlt
    by_contra hnot
    have htrue : checker.test smaller = true := Bool.eq_true_of_not_eq_false hnot
    exact hcore.2 hlt ((checker.exact smaller).1 htrue)

end AutocatalyticCS
