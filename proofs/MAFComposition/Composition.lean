import Mathlib
import proofs.MAFComposition.Threshold

/-!
Parallel composition and reaction-addition laws for the corrected strict MAF
price cone.  These statements retain the price vector, so the intersection is
pointwise; replacing it by a conjunction of two existential statements would
be false.
-/

namespace MAFComposition

open Set

variable {ι κ ρ : Type} [Fintype ι] [Fintype κ] [Fintype ρ]

def Network.parallel (N₁ : Network ι κ) (N₂ : Network ι ρ) :
    Network ι (Sum κ ρ) where
  input := parallelColumns N₁.input N₂.input
  output := parallelColumns N₁.output N₂.output

def Network.priceCone (N : Network ι κ) (q : ℝ) : Set (ι → ℝ) :=
  {p | StrictObstruction N.input N.output q p}

omit [Fintype κ] in
private lemma vecMul_netMatrix (N : Network ι κ) (q : ℝ) (p : ι → ℝ) (r : κ) :
    Matrix.vecMul p (N.netMatrix q) r =
      weightedColumn p N.output r - q * weightedColumn p N.input r := by
  change (∑ i, p i * (N.output i r - q * N.input i r)) =
    (∑ i, p i * N.output i r) - q * ∑ i, p i * N.input i r
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype κ] in
theorem strictPriceAt_iff_exists_obstruction (N : Network ι κ) (q : ℝ) :
    N.StrictPriceAt q ↔ ∃ p, StrictObstruction N.input N.output q p := by
  constructor
  · rintro ⟨p, hp, hcol⟩
    refine ⟨p, hp, fun r => ?_⟩
    have hr := hcol r
    rw [vecMul_netMatrix] at hr
    linarith
  · rintro ⟨p, hp, hcol⟩
    refine ⟨p, hp, fun r => ?_⟩
    rw [vecMul_netMatrix]
    linarith [hcol r]

omit [Fintype κ] [Fintype ρ] in
theorem priceCone_parallel (N₁ : Network ι κ) (N₂ : Network ι ρ) (q : ℝ) :
    (N₁.parallel N₂).priceCone q = N₁.priceCone q ∩ N₂.priceCone q := by
  ext p
  exact strictObstruction_parallel_iff N₁.input N₁.output N₂.input N₂.output q p

omit [Fintype κ] [Fintype ρ] in
theorem strictPriceAt_parallel_iff (N₁ : Network ι κ) (N₂ : Network ι ρ) (q : ℝ) :
    (N₁.parallel N₂).StrictPriceAt q ↔
      ∃ p, p ∈ N₁.priceCone q ∩ N₂.priceCone q := by
  rw [strictPriceAt_iff_exists_obstruction]
  simp only [Network.priceCone, Set.mem_inter_iff, Set.mem_setOf_eq]
  exact exists_congr fun p =>
    strictObstruction_parallel_iff N₁.input N₁.output N₂.input N₂.output q p

theorem feasibleAt_parallel_of_left (N₁ : Network ι κ) (N₂ : Network ι ρ)
    (q : ℝ) (h : N₁.FeasibleAt q) : (N₁.parallel N₂).FeasibleAt q := by
  rw [feasibleAt_iff_not_strictPriceAt]
  intro hprice
  obtain ⟨p, hp₁, _hp₂⟩ := (strictPriceAt_parallel_iff N₁ N₂ q).mp hprice
  have hp : N₁.StrictPriceAt q :=
    (strictPriceAt_iff_exists_obstruction N₁ q).mpr ⟨p, hp₁⟩
  exact (feasibleAt_iff_not_strictPriceAt N₁ q).mp h hp

theorem feasibleAt_parallel_of_right (N₁ : Network ι κ) (N₂ : Network ι ρ)
    (q : ℝ) (h : N₂.FeasibleAt q) : (N₁.parallel N₂).FeasibleAt q := by
  rw [feasibleAt_iff_not_strictPriceAt]
  intro hprice
  obtain ⟨p, _hp₁, hp₂⟩ := (strictPriceAt_parallel_iff N₁ N₂ q).mp hprice
  have hp : N₂.StrictPriceAt q :=
    (strictPriceAt_iff_exists_obstruction N₂ q).mpr ⟨p, hp₂⟩
  exact (feasibleAt_iff_not_strictPriceAt N₂ q).mp h hp

theorem maf_le_parallel_maf_left (N₁ : Network ι κ) (N₂ : Network ι ρ)
    {a c : ℝ} (ha : N₁.IsMAF a) (hc : (N₁.parallel N₂).IsMAF c) : a ≤ c := by
  exact hc.2 a (feasibleAt_parallel_of_left N₁ N₂ a ha.1)

theorem maf_le_parallel_maf_right (N₁ : Network ι κ) (N₂ : Network ι ρ)
    {b c : ℝ} (hb : N₂.IsMAF b) (hc : (N₁.parallel N₂).IsMAF c) : b ≤ c := by
  exact hc.2 b (feasibleAt_parallel_of_right N₁ N₂ b hb.1)

omit [Fintype ι] [Fintype κ] [Fintype ρ] in
theorem inputNonnegative_parallel (N₁ : Network ι κ) (N₂ : Network ι ρ)
    (h₁ : N₁.InputNonnegative) (h₂ : N₂.InputNonnegative) :
    (N₁.parallel N₂).InputNonnegative := by
  intro i r
  cases r with
  | inl r => exact h₁ i r
  | inr r => exact h₂ i r

theorem parallel_isMAF_max_iff_commonPricesAbove
    (N₁ : Network ι κ) (N₂ : Network ι ρ)
    (hA₁ : N₁.InputNonnegative) (hA₂ : N₂.InputNonnegative)
    {a b : ℝ} (ha : N₁.IsMAF a) (hb : N₂.IsMAF b) :
    (N₁.parallel N₂).IsMAF (max a b) ↔
      ∀ q, max a b < q → ∃ p, p ∈ N₁.priceCone q ∩ N₂.priceCone q := by
  constructor
  · intro hmax q hq
    have hp := (hmax.lt_iff_strictPriceAt
      (inputNonnegative_parallel N₁ N₂ hA₁ hA₂) q).mp hq
    exact (strictPriceAt_parallel_iff N₁ N₂ q).mp hp
  · intro hcommon
    constructor
    · rcases le_total a b with hab | hba
      · simpa [max_eq_right hab] using feasibleAt_parallel_of_right N₁ N₂ b hb.1
      · simpa [max_eq_left hba] using feasibleAt_parallel_of_left N₁ N₂ a ha.1
    · intro q hq
      by_contra hnot
      have hlt : max a b < q := lt_of_not_ge hnot
      obtain ⟨p, hp⟩ := hcommon q hlt
      have hprice : (N₁.parallel N₂).StrictPriceAt q :=
        (strictPriceAt_parallel_iff N₁ N₂ q).mpr ⟨p, hp⟩
      exact (feasibleAt_iff_not_strictPriceAt (N₁.parallel N₂) q).mp hq hprice

theorem parallel_strictSynergy_iff_no_commonPricesAbove
    (N₁ : Network ι κ) (N₂ : Network ι ρ)
    (hA₁ : N₁.InputNonnegative) (hA₂ : N₂.InputNonnegative)
    {a b c : ℝ} (ha : N₁.IsMAF a) (hb : N₂.IsMAF b)
    (hc : (N₁.parallel N₂).IsMAF c) :
    max a b < c ↔
      ¬ ∀ q, max a b < q → ∃ p, p ∈ N₁.priceCone q ∩ N₂.priceCone q := by
  have hle : max a b ≤ c := max_le
    (maf_le_parallel_maf_left N₁ N₂ ha hc)
    (maf_le_parallel_maf_right N₁ N₂ hb hc)
  rw [← parallel_isMAF_max_iff_commonPricesAbove N₁ N₂ hA₁ hA₂ ha hb]
  constructor
  · intro hlt heq
    have := hc.unique heq
    linarith
  · intro hne
    exact lt_of_le_of_ne hle fun heq => hne (heq ▸ hc)

end MAFComposition
