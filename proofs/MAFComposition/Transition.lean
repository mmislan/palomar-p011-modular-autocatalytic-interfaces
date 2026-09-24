import Mathlib
import proofs.MAFComposition.Gordan

/-!
The exact strict-production/weak-price alternative.  It is obtained from the
already verified strict Gordan theorem by applying it to `-Cᵀ`; this explains
why fixed-threshold MAF needs a strict dual, while transition productivity uses
a weak dual with a nonzero price.
-/

namespace MAFComposition

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]

def StrictProductive (C : Matrix ι κ ℝ) : Prop :=
  ∃ x : κ → ℝ, (∀ r, 0 ≤ x r) ∧ x ≠ 0 ∧ ∀ i, 0 < C.mulVec x i

def WeakColumnDual (C : Matrix ι κ ℝ) : Prop :=
  ∃ p : ι → ℝ, (∀ i, 0 ≤ p i) ∧ p ≠ 0 ∧ ∀ r, Matrix.vecMul p C r ≤ 0

omit [Fintype κ] [Nonempty ι] in
private lemma neg_transpose_mulVec (C : Matrix ι κ ℝ) (p : ι → ℝ) (r : κ) :
    (-C.transpose).mulVec p r = -Matrix.vecMul p C r := by
  change (∑ i, (-C i r) * p i) = -(∑ i, p i * C i r)
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype ι] [Nonempty ι] in
private lemma vecMul_neg_transpose (C : Matrix ι κ ℝ) (x : κ → ℝ) (i : ι) :
    Matrix.vecMul x (-C.transpose) i = -C.mulVec x i := by
  change (∑ r, x r * (-C i r)) = -(∑ r, C i r * x r)
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

omit [Fintype κ] [Nonempty ι] in
theorem primal_neg_transpose_iff_weakColumnDual (C : Matrix ι κ ℝ) :
    PrimalNonnegative (-C.transpose) ↔ WeakColumnDual C := by
  constructor
  · rintro ⟨p, hp, hpne, hcol⟩
    refine ⟨p, hp, hpne, fun r => ?_⟩
    have hr := hcol r
    rw [neg_transpose_mulVec] at hr
    linarith
  · rintro ⟨p, hp, hpne, hcol⟩
    refine ⟨p, hp, hpne, fun r => ?_⟩
    rw [neg_transpose_mulVec]
    linarith [hcol r]

omit [Fintype ι] in
theorem strictColumnDual_neg_transpose_iff_strictProductive
    (C : Matrix ι κ ℝ) : StrictColumnDual (-C.transpose) ↔ StrictProductive C := by
  constructor
  · rintro ⟨x, hx, hstrict⟩
    refine ⟨x, hx, ?_, fun i => ?_⟩
    · intro hzero
      obtain ⟨i⟩ := ‹Nonempty ι›
      have hi := hstrict i
      simp [hzero, vecMul_neg_transpose] at hi
    · have hi := hstrict i
      rw [vecMul_neg_transpose] at hi
      linarith
  · rintro ⟨x, hx, _hxne, hstrict⟩
    refine ⟨x, hx, fun i => ?_⟩
    rw [vecMul_neg_transpose]
    linarith [hstrict i]

theorem strictProductive_iff_not_weakColumnDual (C : Matrix ι κ ℝ) :
    StrictProductive C ↔ ¬ WeakColumnDual C := by
  rw [← strictColumnDual_neg_transpose_iff_strictProductive,
    ← primal_neg_transpose_iff_weakColumnDual]
  exact (strict_gordan_alternative (-C.transpose)).symm

theorem weakColumnDual_iff_not_strictProductive (C : Matrix ι κ ℝ) :
    WeakColumnDual C ↔ ¬ StrictProductive C := by
  rw [strictProductive_iff_not_weakColumnDual]
  tauto

end MAFComposition
