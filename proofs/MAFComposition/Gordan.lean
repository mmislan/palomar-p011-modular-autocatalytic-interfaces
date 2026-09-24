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

/-- Probability vectors on a finite index type.  This local set replaces the
finite-function `stdSimplex`, which the pinned Mathlib deprecates in favour of a
separate `StdSimplex` type. -/
def simplex (κ : Type*) [Fintype κ] : Set (κ → ℝ) :=
  {x | (∀ r, 0 ≤ x r) ∧ ∑ r, x r = 1}

theorem convex_simplex : Convex ℝ (simplex κ) := by
  refine fun f hf g hg a b ha hb hab => ⟨fun x => ?_, ?_⟩
  · apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1]
  · simp_rw [Pi.add_apply, Pi.smul_apply]
    rwa [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hf.2, hg.2, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one]

theorem isCompact_simplex : IsCompact (simplex κ) := by
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : κ → ℝ)) (b := 1))
  · have h1 : IsClosed {x : κ → ℝ | ∀ r, 0 ≤ x r} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun r => isClosed_le continuous_const (continuous_apply r)
    have h2 : IsClosed {x : κ → ℝ | ∑ r, x r = 1} :=
      isClosed_eq (continuous_finsetSum _ fun r _ => continuous_apply r) continuous_const
    rw [simplex, Set.ofPred_and]
    exact h1.inter h2
  · rintro x ⟨hx0, hx1⟩
    refine ⟨fun r => hx0 r, fun r => ?_⟩
    have := Finset.single_le_sum (fun j _ => hx0 j) (Finset.mem_univ r)
    simpa [hx1] using this

theorem single_mem_simplex [DecidableEq κ] (r : κ) : Pi.single r 1 ∈ simplex κ :=
  ⟨fun i => by by_cases h : i = r <;> simp [h], by simp⟩

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

theorem not_primal_implies_strictColumnDual (C : Matrix ι κ ℝ)
    (hno : ¬ PrimalNonnegative C) : StrictColumnDual C := by
  classical
  let K : Set (ι → ℝ) := C.mulVecLin '' simplex κ
  have hKconv : Convex ℝ K :=
    (convex_simplex (κ := κ)).linear_image C.mulVecLin
  have hKcomp : IsCompact K :=
    (isCompact_simplex (κ := κ)).image
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
    have hvertex : (Pi.basisFun ℝ κ) r ∈ simplex κ := by
      simpa [Pi.basisFun_apply] using single_mem_simplex r
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
