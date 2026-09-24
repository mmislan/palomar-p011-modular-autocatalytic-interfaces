import Mathlib
import proofs.MAFComposition.Threshold

/-!
Universal monotone simulation order.  The threshold-feasibility preorder is the
minimal interface needed by all composition/edit maps; scalar MAF monotonicity
is a single consequence rather than a separate proof for every operation.
-/

namespace MAFComposition

variable {ι ζ κ ρ : Type} [Fintype ι] [Fintype ζ] [Fintype κ] [Fintype ρ]

def Network.ThresholdSimulates (N : Network ι κ) (M : Network ζ ρ) : Prop :=
  ∀ q, N.FeasibleAt q → M.FeasibleAt q

omit [Fintype ι] in
theorem Network.ThresholdSimulates.refl (N : Network ι κ) :
    N.ThresholdSimulates N := by
  intro q h
  exact h

omit [Fintype ι] [Fintype ζ] in
theorem Network.ThresholdSimulates.trans {N : Network ι κ} {M : Network ζ ρ}
    {υ σ : Type} [Fintype υ] [Fintype σ] {L : Network υ σ}
    (hNM : N.ThresholdSimulates M) (hML : M.ThresholdSimulates L) :
    N.ThresholdSimulates L := by
  intro q hq
  exact hML q (hNM q hq)

omit [Fintype ι] [Fintype ζ] in
theorem maf_le_of_thresholdSimulates {N : Network ι κ} {M : Network ζ ρ}
    {a b : ℝ} (hNM : N.ThresholdSimulates M)
    (ha : N.IsMAF a) (hb : M.IsMAF b) : a ≤ b := by
  exact hb.2 a (hNM a ha.1)

def Network.Dominates (N M : Network ι κ) : Prop :=
  (∀ i r, M.input i r ≤ N.input i r) ∧
  (∀ i r, N.output i r ≤ M.output i r)

omit [Fintype ι] in
theorem dominates_feasibleAt {N M : Network ι κ} (hdom : N.Dominates M)
    {q : ℝ} (hq : 0 ≤ q) (h : N.FeasibleAt q) : M.FeasibleAt q := by
  rcases h with ⟨x, hx, hxne, hineq⟩
  refine ⟨x, hx, hxne, fun i => ?_⟩
  have hinput : M.input.mulVec x i ≤ N.input.mulVec x i := by
    exact Finset.sum_le_sum fun r _ =>
      mul_le_mul_of_nonneg_right (hdom.1 i r) (hx r)
  have houtput : N.output.mulVec x i ≤ M.output.mulVec x i := by
    exact Finset.sum_le_sum fun r _ =>
      mul_le_mul_of_nonneg_right (hdom.2 i r) (hx r)
  exact (mul_le_mul_of_nonneg_left hinput hq).trans ((hineq i).trans houtput)

omit [Fintype ι] in
theorem maf_le_of_dominates {N M : Network ι κ} (hdom : N.Dominates M)
    {a b : ℝ} (ha0 : 0 ≤ a) (ha : N.IsMAF a) (hb : M.IsMAF b) : a ≤ b := by
  exact hb.2 a (dominates_feasibleAt hdom ha0 ha.1)

end MAFComposition
