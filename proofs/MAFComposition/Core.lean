import Mathlib

/-!
Kernel-checked core facts for the MAF composition audit.

`RatioAtLeast` implements the paper convention that a species with zero input
does not constrain the output/input minimum.  `ExactThreshold` avoids choosing
an analytic definition of the supremum: it packages a feasible lower witness
and a proof that every feasible threshold is no larger.
-/

namespace MAFComposition

def RatioAtLeast {ι : Type} (input output : ι → ℝ) (q : ℝ) : Prop :=
  ∀ i, input i = 0 ∨ q ≤ output i / input i

theorem ratioAtLeast_iff {ι : Type} (input output : ι → ℝ) (q : ℝ)
    (hinput : ∀ i, 0 ≤ input i) (houtput : ∀ i, 0 ≤ output i) :
    RatioAtLeast input output q ↔ ∀ i, q * input i ≤ output i := by
  constructor
  · intro h i
    rcases h i with hzero | hratio
    · simpa [hzero] using houtput i
    · by_cases hzero : input i = 0
      · simpa [hzero] using houtput i
      · have hpos : 0 < input i := lt_of_le_of_ne (hinput i) (Ne.symm hzero)
        exact (le_div_iff₀ hpos).mp hratio
  · intro h i
    by_cases hi : input i = 0
    · exact Or.inl hi
    · exact Or.inr ((le_div_iff₀ (lt_of_le_of_ne (hinput i) (Ne.symm hi))).mpr (h i))

def ExactThreshold (F : ℝ → Prop) (a : ℝ) : Prop :=
  F a ∧ ∀ q, F q → q ≤ a

-- N1: A → B and B → 4A.
def N1Feasible (q : ℝ) : Prop :=
  ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ (x ≠ 0 ∨ y ≠ 0) ∧
    q * x ≤ 4 * y ∧ q * y ≤ x

-- N2: A → 4B and B → A.
def N2Feasible (q : ℝ) : Prop :=
  ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ (x ≠ 0 ∨ y ≠ 0) ∧
    q * x ≤ y ∧ q * y ≤ 4 * x

theorem n1_exact : ExactThreshold N1Feasible 2 := by
  constructor
  · exact ⟨2, 1, by norm_num, by norm_num, Or.inl (by norm_num), by norm_num, by norm_num⟩
  · rintro q ⟨x, y, hx, hy, hne, hA, hB⟩
    have hden : 0 < x + 2 * y := by
      rcases hne with hne | hne
      · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
        nlinarith
      · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hne)
        nlinarith
    have hweighted : q * (x + 2 * y) ≤ 2 * (x + 2 * y) := by
      nlinarith
    nlinarith

theorem n2_exact : ExactThreshold N2Feasible 2 := by
  constructor
  · exact ⟨1, 2, by norm_num, by norm_num, Or.inl (by norm_num), by norm_num, by norm_num⟩
  · rintro q ⟨x, y, hx, hy, hne, hA, hB⟩
    have hden : 0 < 2 * x + y := by
      rcases hne with hne | hne
      · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
        nlinarith
      · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hne)
        nlinarith
    have hweighted : q * (2 * x + y) ≤ 2 * (2 * x + y) := by
      nlinarith
    nlinarith

-- Parallel composition of N1 with another copy of N1.
def N1N1Feasible (q : ℝ) : Prop :=
  ∃ a b c d : ℝ,
    0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧
    (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) ∧
    q * (a + c) ≤ 4 * (b + d) ∧ q * (b + d) ≤ a + c

theorem n1n1_exact : ExactThreshold N1N1Feasible 2 := by
  constructor
  · exact ⟨2, 1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num,
      Or.inl (by norm_num), by norm_num, by norm_num⟩
  · rintro q ⟨a, b, c, d, ha, hb, hc, hd, hne, hA, hB⟩
    have hden : 0 < (a + c) + 2 * (b + d) := by
      rcases hne with hne | hne | hne | hne
      · have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm hne); nlinarith
      · have hpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hne); nlinarith
      · have hpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hne); nlinarith
      · have hpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hne); nlinarith
    have hweighted :
        q * ((a + c) + 2 * (b + d)) ≤ 2 * ((a + c) + 2 * (b + d)) := by
      nlinarith
    nlinarith

-- Parallel composition N2 || N1, ordered as N2's two reactions then N1's.
def N2N1Feasible (q : ℝ) : Prop :=
  ∃ a b c d : ℝ,
    0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧
    (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) ∧
    q * (a + c) ≤ b + 4 * d ∧ q * (b + d) ≤ 4 * a + c

theorem n2n1_exact : ExactThreshold N2N1Feasible 4 := by
  constructor
  · exact ⟨1, 0, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num,
      Or.inl (by norm_num), by norm_num, by norm_num⟩
  · rintro q ⟨a, b, c, d, ha, hb, hc, hd, hne, hA, hB⟩
    have hden : 0 < a + b + c + d := by
      rcases hne with hne | hne | hne | hne
      · have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm hne); nlinarith
      · have hpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hne); nlinarith
      · have hpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hne); nlinarith
      · have hpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hne); nlinarith
    have hweighted : q * (a + b + c + d) ≤ 4 * (a + b + c + d) := by
      nlinarith
    nlinarith

/- Two networks and the common partner all have exact threshold 2, but the
parallel outcomes have exact thresholds 2 and 4.  Therefore no scalar-only
binary rule can determine shared-species parallel composition. -/
theorem scalar_parallel_composition_impossible :
    ExactThreshold N1Feasible 2 ∧ ExactThreshold N2Feasible 2 ∧
    ExactThreshold N1N1Feasible 2 ∧ ExactThreshold N2N1Feasible 4 :=
  ⟨n1_exact, n2_exact, n1n1_exact, n2n1_exact⟩

-- Reducible autonomous network with reactions A → 2A and B → B.
def ReducibleFeasible (q : ℝ) : Prop :=
  ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ (x ≠ 0 ∨ y ≠ 0) ∧
    q * x ≤ 2 * x ∧ q * y ≤ y

def ReducibleWeakK (q pA pB : ℝ) : Prop :=
  0 ≤ pA ∧ 0 ≤ pB ∧ (pA ≠ 0 ∨ pB ≠ 0) ∧
    2 * pA ≤ q * pA ∧ pB ≤ q * pB

theorem reducible_exact : ExactThreshold ReducibleFeasible 2 := by
  constructor
  · exact ⟨1, 0, by norm_num, by norm_num, Or.inl (by norm_num), by norm_num, by norm_num⟩
  · rintro q ⟨x, y, hx, hy, hne, hA, hB⟩
    rcases hne with hxne | hyne
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxne)
      nlinarith
    · by_cases hxzero : x = 0
      · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hyne)
        have hq : q ≤ 1 := by nlinarith
        linarith
      · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
        nlinarith

theorem reducible_weakK_at_one : ReducibleWeakK 1 0 1 := by
  norm_num [ReducibleWeakK]

/- The proposed equivalence `K_N(q) ≠ ∅ ↔ MAF(N) ≤ q`, with merely
semipositive prices, is false even for an autonomous network. -/
theorem semipositive_K_threshold_false :
    ExactThreshold ReducibleFeasible 2 ∧ ReducibleWeakK 1 0 1 :=
  ⟨reducible_exact, reducible_weakK_at_one⟩

end MAFComposition
