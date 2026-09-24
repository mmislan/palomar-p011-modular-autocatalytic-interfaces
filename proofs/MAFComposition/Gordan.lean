import Mathlib
import proofs.MAFComposition.DualCalculus

/-!
Finite strict Gordan alternative for the MAF threshold problem.
-/

namespace MAFComposition

open Set
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def PrimalNonnegative (C : Matrix ι κ ℝ) : Prop :=
  ∃ x : κ → ℝ, (∀ r, 0 ≤ x r) ∧ x ≠ 0 ∧ ∀ i, 0 ≤ C.mulVec x i

def StrictColumnDual (C : Matrix ι κ ℝ) : Prop :=
  ∃ p : ι → ℝ, (∀ i, 0 ≤ p i) ∧ ∀ r, Matrix.vecMul p C r < 0

private lemma continuousLinear_apply_eq_sum_single
    (f : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) :
    f v = ∑ i, v i * f ((Pi.basisFun ℝ ι) i) := by
  classical
  have hv : (∑ i, v i • (Pi.basisFun ℝ ι) i) = v := by
    simpa using (Pi.basisFun ℝ ι).sum_repr v
  calc
    f v = f (∑ i, v i • (Pi.basisFun ℝ ι) i) := congrArg f hv.symm
    _ = ∑ i, f (v i • (Pi.basisFun ℝ ι) i) :=
      map_sum f (fun i => v i • (Pi.basisFun ℝ ι) i) Finset.univ
    _ = ∑ i, v i * f ((Pi.basisFun ℝ ι) i) := by simp [map_smul]

private lemma nonzero_nonnegative_has_pos {x : κ → ℝ}
    (hx : ∀ r, 0 ≤ x r) (hne : x ≠ 0) : ∃ r, 0 < x r := by
  by_contra h
  push Not at h
  apply hne
  funext r
  exact le_antisymm (h r) (hx r)

theorem strictColumnDual_excludes_primal (C : Matrix ι κ ℝ) :
    StrictColumnDual C → ¬ PrimalNonnegative C := by
  rintro ⟨p, hp, hdual⟩ ⟨x, hx, hxne, hCx⟩
  obtain ⟨r₀, hr₀⟩ := nonzero_nonnegative_has_pos hx hxne
  have hleft : 0 ≤ p ⬝ᵥ C.mulVec x := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hCx i)
  have hright : Matrix.vecMul p C ⬝ᵥ x < 0 := by
    have hs :
        (∑ r, Matrix.vecMul p C r * x r) < ∑ _r : κ, (0 : ℝ) := by
      apply Finset.sum_lt_sum
      · intro r _
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (hdual r)) (hx r)
      · exact ⟨r₀, Finset.mem_univ r₀, mul_neg_of_neg_of_pos (hdual r₀) hr₀⟩
    simpa [dotProduct] using hs
  rw [Matrix.dotProduct_mulVec] at hleft
  linarith

-- The pinned Mathlib keeps the finite-function simplex API as deprecated
-- compatibility declarations; retain this representation in the separation proof.
set_option linter.deprecated false in
theorem not_primal_implies_strictColumnDual (C : Matrix ι κ ℝ)
    (hno : ¬ PrimalNonnegative C) : StrictColumnDual C := by
  classical
  let K : Set (ι → ℝ) := C.mulVecLin '' stdSimplex ℝ κ
  have hKconv : Convex ℝ K :=
    (convex_stdSimplex ℝ κ).linear_image C.mulVecLin
  have hKcomp : IsCompact K :=
    (isCompact_stdSimplex ℝ κ).image
      (LinearMap.continuous_of_finiteDimensional C.mulVecLin)
  have hdisj : Disjoint K (ProperCone.positive ℝ (ι → ℝ) : Set (ι → ℝ)) := by
    refine Set.disjoint_left.2 ?_
    intro y hyK hypos
    rcases hyK with ⟨x, hx, rfl⟩
    apply hno
    refine ⟨x, hx.1, ?_, ?_⟩
    · intro hzero
      have : (∑ r, x r) = 0 := by simp [hzero]
      linarith [hx.2]
    · exact (ProperCone.mem_positive.mp hypos)
  obtain ⟨f, hfpos, hfK⟩ :=
    (ProperCone.positive ℝ (ι → ℝ)).hyperplane_separation hKconv hKcomp hdisj
  let p : ι → ℝ := fun i => f ((Pi.basisFun ℝ ι) i)
  refine ⟨p, ?_, ?_⟩
  · intro i
    apply hfpos ((Pi.basisFun ℝ ι) i)
    simp [ProperCone.mem_positive, Pi.basisFun_apply]
  · intro r
    have hvertex : (Pi.basisFun ℝ κ) r ∈ stdSimplex ℝ κ := by
      simpa [Pi.basisFun_apply] using single_mem_stdSimplex ℝ r
    have hstrict := hfK (C.mulVec ((Pi.basisFun ℝ κ) r))
      ⟨(Pi.basisFun ℝ κ) r, hvertex, rfl⟩
    have hcol : C.mulVec ((Pi.basisFun ℝ κ) r) = fun i => C i r := by
      ext i
      simp [Matrix.mulVec, Pi.basisFun_apply]
    rw [hcol] at hstrict
    rw [continuousLinear_apply_eq_sum_single] at hstrict
    simpa [p, Matrix.vecMul, dotProduct, Pi.basisFun_apply, mul_comm] using hstrict

theorem strict_gordan_alternative (C : Matrix ι κ ℝ) :
    (¬ PrimalNonnegative C) ↔ StrictColumnDual C := by
  constructor
  · exact not_primal_implies_strictColumnDual C
  · exact strictColumnDual_excludes_primal C

theorem primal_iff_not_strictColumnDual (C : Matrix ι κ ℝ) :
    PrimalNonnegative C ↔ ¬ StrictColumnDual C := by
  rw [← strict_gordan_alternative C]
  tauto

end MAFComposition
