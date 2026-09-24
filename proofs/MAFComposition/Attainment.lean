import Mathlib
import proofs.MAFComposition.Threshold

/-!
Finite-dimensional attainment bridge.  Once source-domain arguments provide a
finite upper bound on feasible thresholds, the maximum in `Network.IsMAF` is
not an extra assumption: normalization to the standard simplex and compactness
produce an attained MAF.
-/

namespace MAFComposition

open Set

variable {ι κ : Type} [Fintype ι] [Fintype κ] [Nonempty κ]

def Network.ThresholdBoundedAbove (N : Network ι κ) (U : ℝ) : Prop :=
  ∀ q, N.FeasibleAt q → q ≤ U

private def normalizedFeasiblePairs (N : Network ι κ) (U : ℝ) :
    Set (ℝ × (κ → ℝ)) :=
  {z | z.1 ∈ Set.Icc 0 U ∧ z.2 ∈ stdSimplex ℝ κ ∧
    ∀ i, z.1 * N.input.mulVec z.2 i ≤ N.output.mulVec z.2 i}

omit [Fintype ι] [Nonempty κ] in
private theorem normalizedFeasiblePairs_compact (N : Network ι κ) (U : ℝ) :
    IsCompact (normalizedFeasiblePairs N U) := by
  let base : Set (ℝ × (κ → ℝ)) := Set.Icc 0 U ×ˢ stdSimplex ℝ κ
  let constraints : Set (ℝ × (κ → ℝ)) :=
    ⋂ i, {z | z.1 * N.input.mulVec z.2 i ≤ N.output.mulVec z.2 i}
  have hbase : IsCompact base := isCompact_Icc.prod (isCompact_stdSimplex ℝ κ)
  have hconstraints : IsClosed constraints := by
    apply isClosed_iInter
    intro i
    apply isClosed_le
    · fun_prop
    · fun_prop
  have heq : normalizedFeasiblePairs N U = base ∩ constraints := by
    ext z
    simp only [normalizedFeasiblePairs, base, constraints, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc, Set.mem_iInter]
    tauto
  rw [heq]
  exact hbase.inter_right hconstraints

omit [Nonempty κ] in
private lemma sum_pos_of_nonnegative_ne_zero {x : κ → ℝ}
    (hx : ∀ r, 0 ≤ x r) (hxne : x ≠ 0) : 0 < ∑ r, x r := by
  have hnonneg : 0 ≤ ∑ r, x r := Finset.sum_nonneg fun r _ => hx r
  refine lt_of_le_of_ne hnonneg ?_
  intro hsum0
  apply hxne
  funext r
  exact
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hx j)).mp hsum0.symm r
      (Finset.mem_univ r)

omit [Fintype ι] [Nonempty κ] in
private lemma mulVec_div_sum (M : Matrix ι κ ℝ) (x : κ → ℝ)
    (s : ℝ) (i : ι) :
    M.mulVec (fun r => x r / s) i = M.mulVec x i / s := by
  change (∑ r, M i r * (x r / s)) = (∑ r, M i r * x r) / s
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  ring

omit [Nonempty κ] in
private lemma sum_mulVec_all (M : Matrix ι κ ℝ) (x : κ → ℝ) :
    (∑ i, M.mulVec x i) = ∑ r, (∑ i, M i r) * x r := by
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm

omit [Fintype ι] in
theorem exists_isMAF_of_bounded
    (N : Network ι κ) (hB : N.OutputNonnegative)
    {U : ℝ} (hU : 0 ≤ U) (hbound : N.ThresholdBoundedAbove U) :
    ∃ a, N.IsMAF a := by
  classical
  let K := normalizedFeasiblePairs N U
  have hKcompact : IsCompact K := normalizedFeasiblePairs_compact N U
  have hKne : K.Nonempty := by
    let r₀ : κ := Classical.choice ‹Nonempty κ›
    let x : κ → ℝ := Pi.single r₀ 1
    refine ⟨(0, x), ?_⟩
    refine ⟨⟨le_rfl, hU⟩, ?_, ?_⟩
    · simpa [x] using single_mem_stdSimplex ℝ r₀
    · intro i
      have hi : 0 ≤ N.output.mulVec x i := by
        simpa [x] using hB i r₀
      simpa using hi
  obtain ⟨z, hzK, hzmax⟩ :=
    hKcompact.exists_isMaxOn hKne continuous_fst.continuousOn
  refine ⟨z.1, ?_, ?_⟩
  · refine ⟨z.2, hzK.2.1.1, ?_, hzK.2.2⟩
    intro hzero
    have hsum := hzK.2.1.2
    simp [hzero] at hsum
  · intro q hq
    by_cases hq0 : q ≤ 0
    · exact hq0.trans hzK.1.1
    · rcases hq with ⟨x, hx, hxne, hineq⟩
      let s : ℝ := ∑ r, x r
      have hs : 0 < s := sum_pos_of_nonnegative_ne_zero hx hxne
      let y : κ → ℝ := fun r => x r / s
      have hySimplex : y ∈ stdSimplex ℝ κ := by
        refine ⟨fun r => div_nonneg (hx r) (le_of_lt hs), ?_⟩
        change (∑ r, x r / s) = 1
        rw [← Finset.sum_div]
        exact div_self (ne_of_gt hs)
      have hyineq : ∀ i, q * N.input.mulVec y i ≤ N.output.mulVec y i := by
        intro i
        rw [mulVec_div_sum (M := N.input) (x := x) s i,
          mulVec_div_sum (M := N.output) (x := x) s i]
        have hi := (div_le_div_iff_of_pos_right hs).mpr (hineq i)
        convert hi using 1
        all_goals ring
      have hqK : (q, y) ∈ K := by
        exact ⟨⟨le_of_not_ge hq0, hbound q ⟨x, hx, hxne, hineq⟩⟩,
          hySimplex, hyineq⟩
      exact hzmax hqK

/-- A directly checkable CRN-domain attainment criterion.  If every reaction
consumes a positive total amount and total product is at most `U` times total
reactant for each reaction, then every feasible threshold is at most `U`, so
the compact-attainment theorem applies. -/
theorem exists_isMAF_of_columnBound
    (N : Network ι κ) (hB : N.OutputNonnegative)
    {U : ℝ} (hU : 0 ≤ U)
    (hinput : ∀ r, 0 < ∑ i, N.input i r)
    (hcolumn : ∀ r, (∑ i, N.output i r) ≤ U * ∑ i, N.input i r) :
    ∃ a, N.IsMAF a := by
  apply exists_isMAF_of_bounded N hB hU
  intro q hq
  rcases hq with ⟨x, hx, hxne, hineq⟩
  have hxpos : ∃ r, 0 < x r := by
    by_contra h
    push Not at h
    apply hxne
    funext r
    exact le_antisymm (h r) (hx r)
  have htotalpos : 0 < ∑ i, N.input.mulVec x i := by
    have hweighted : 0 < ∑ r, (∑ i, N.input i r) * x r := by
      apply Finset.sum_pos'
      · intro r _
        exact mul_nonneg (le_of_lt (hinput r)) (hx r)
      · obtain ⟨r, hr⟩ := hxpos
        exact ⟨r, Finset.mem_univ r, mul_pos (hinput r) hr⟩
    rw [sum_mulVec_all]
    exact hweighted
  have hfeasibleSum :
      q * (∑ i, N.input.mulVec x i) ≤ ∑ i, N.output.mulVec x i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hineq i
  have hcolumnSum :
      (∑ i, N.output.mulVec x i) ≤ U * ∑ i, N.input.mulVec x i := by
    calc
      (∑ i, N.output.mulVec x i) =
          ∑ r, (∑ i, N.output i r) * x r := by
            rw [sum_mulVec_all]
      _ ≤ ∑ r, (U * ∑ i, N.input i r) * x r :=
        Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hcolumn r) (hx r)
      _ = U * ∑ i, N.input.mulVec x i := by
        rw [sum_mulVec_all, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
  nlinarith

end MAFComposition
