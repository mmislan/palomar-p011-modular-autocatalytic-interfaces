import proofs.AutocatalyticCS.SourceCandidateCompleteness
import proofs.AutocatalyticCS.ExactSemipositivity

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

/-- A concrete exact-recognition boundary.  A `true` answer carries a rational
primal witness for a matching with these edges.  A `false` answer carries a
rational Gordan--Stiemke obstruction for every representation of those edges.
All fields are checked by Lean using exact rational arithmetic. -/
structure CertifiedAutocatalyticTest (Q : ReactionNetwork X R) where
  test : Finset (X × R) → Bool
  positive : ∀ edges, test edges = true →
    ∃ E : IndexedMatching Q, E.edgeFinset = edges ∧
      Nonempty (PositiveRationalCertificate E)
  negative : ∀ edges, test edges = false →
    ∀ E : IndexedMatching Q, E.edgeFinset = edges →
      NegativeRationalCertificate E

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
    exact (checker.negative edges hfalse E hE).not_autocatalytic hauto

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
