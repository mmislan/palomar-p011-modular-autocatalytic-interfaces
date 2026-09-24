import Mathlib
import proofs.MAFComposition.Gordan

/-!
Source-faithful fixed-threshold semantics and the exact strict dual theorem for
an attained Maximum Amplification Factor.
-/

namespace MAFComposition

variable {ι κ : Type} [Fintype ι] [Fintype κ]

structure Network (ι κ : Type) where
  input : Matrix ι κ ℝ
  output : Matrix ι κ ℝ

def Network.InputNonnegative (N : Network ι κ) : Prop :=
  ∀ i r, 0 ≤ N.input i r

def Network.OutputNonnegative (N : Network ι κ) : Prop :=
  ∀ i r, 0 ≤ N.output i r

def Network.FeasibleAt (N : Network ι κ) (q : ℝ) : Prop :=
  ∃ x : κ → ℝ, (∀ r, 0 ≤ x r) ∧ x ≠ 0 ∧
    ∀ i, q * N.input.mulVec x i ≤ N.output.mulVec x i

def Network.IsMAF (N : Network ι κ) (a : ℝ) : Prop :=
  N.FeasibleAt a ∧ ∀ q, N.FeasibleAt q → q ≤ a

def Network.netMatrix (N : Network ι κ) (q : ℝ) : Matrix ι κ ℝ :=
  fun i r => N.output i r - q * N.input i r

def Network.StrictPriceAt (N : Network ι κ) (q : ℝ) : Prop :=
  StrictColumnDual (N.netMatrix q)

omit [Fintype ι] in
private lemma netMatrix_mulVec (N : Network ι κ) (q : ℝ) (x : κ → ℝ) (i : ι) :
    (N.netMatrix q).mulVec x i =
      N.output.mulVec x i - q * N.input.mulVec x i := by
  change (∑ j, (N.output i j - q * N.input i j) * x j) =
    (∑ j, N.output i j * x j) - q * ∑ j, N.input i j * x j
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype ι] in
theorem feasibleAt_iff_primal (N : Network ι κ) (q : ℝ) :
    N.FeasibleAt q ↔ PrimalNonnegative (N.netMatrix q) := by
  constructor
  · rintro ⟨x, hx, hxne, hineq⟩
    refine ⟨x, hx, hxne, fun i => ?_⟩
    rw [netMatrix_mulVec]
    linarith [hineq i]
  · rintro ⟨x, hx, hxne, hnet⟩
    refine ⟨x, hx, hxne, fun i => ?_⟩
    have hi := hnet i
    rw [netMatrix_mulVec] at hi
    linarith

theorem not_feasibleAt_iff_strictPriceAt (N : Network ι κ) (q : ℝ) :
    (¬ N.FeasibleAt q) ↔ N.StrictPriceAt q := by
  rw [feasibleAt_iff_primal, Network.StrictPriceAt, strict_gordan_alternative]

theorem feasibleAt_iff_not_strictPriceAt (N : Network ι κ) (q : ℝ) :
    N.FeasibleAt q ↔ ¬ N.StrictPriceAt q := by
  rw [feasibleAt_iff_primal, Network.StrictPriceAt, primal_iff_not_strictColumnDual]

omit [Fintype ι] in
theorem feasibleAt_anti (N : Network ι κ) (hA : N.InputNonnegative)
    {q r : ℝ} (hqr : q ≤ r) (hr : N.FeasibleAt r) : N.FeasibleAt q := by
  rcases hr with ⟨x, hx, hxne, hineq⟩
  refine ⟨x, hx, hxne, fun i => ?_⟩
  have hAx : 0 ≤ N.input.mulVec x i := by
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hx j)
  exact (mul_le_mul_of_nonneg_right hqr hAx).trans (hineq i)

omit [Fintype ι] in
theorem Network.IsMAF.unique {N : Network ι κ} {a b : ℝ}
    (ha : N.IsMAF a) (hb : N.IsMAF b) : a = b := by
  exact le_antisymm (hb.2 a ha.1) (ha.2 b hb.1)

theorem Network.IsMAF.lt_iff_strictPriceAt {N : Network ι κ}
    (hA : N.InputNonnegative) {a : ℝ} (ha : N.IsMAF a) (q : ℝ) :
    a < q ↔ N.StrictPriceAt q := by
  constructor
  · intro haq
    apply (not_feasibleAt_iff_strictPriceAt N q).mp
    intro hq
    exact (not_le_of_gt haq) (ha.2 q hq)
  · intro hdual
    have hnq : ¬ N.FeasibleAt q :=
      (not_feasibleAt_iff_strictPriceAt N q).mpr hdual
    by_contra hnot
    have hqa : q ≤ a := le_of_not_gt hnot
    exact hnq (feasibleAt_anti N hA hqa ha.1)

end MAFComposition
