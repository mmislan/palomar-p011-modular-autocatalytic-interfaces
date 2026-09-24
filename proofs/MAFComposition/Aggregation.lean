import Mathlib
import proofs.MAFComposition.Composition

/-!
Nonnegative species aggregation.  Primal witnesses push forward through the
aggregation matrix, while a strict price on the aggregated species lifts by
left multiplication to a strict price on the original species.
-/

namespace MAFComposition

variable {ι ζ κ : Type} [Fintype ι] [Fintype ζ] [Fintype κ]

def Matrix.EntrywiseNonnegative (C : Matrix ζ ι ℝ) : Prop :=
  ∀ z i, 0 ≤ C z i

def Network.aggregate (C : Matrix ζ ι ℝ) (N : Network ι κ) : Network ζ κ where
  input := C * N.input
  output := C * N.output

omit [Fintype ζ] in
theorem feasibleAt_aggregate (C : Matrix ζ ι ℝ) (hC : Matrix.EntrywiseNonnegative C)
    (N : Network ι κ) (q : ℝ) (h : N.FeasibleAt q) :
    (N.aggregate C).FeasibleAt q := by
  rcases h with ⟨x, hx, hxne, hineq⟩
  refine ⟨x, hx, hxne, fun z => ?_⟩
  have hsum :
      (∑ i, C z i * (q * N.input.mulVec x i)) ≤
        ∑ i, C z i * N.output.mulVec x i := by
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hineq i) (hC z i)
  change q * (C * N.input).mulVec x z ≤ (C * N.output).mulVec x z
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change q * (∑ i, C z i * N.input.mulVec x i) ≤
    ∑ i, C z i * N.output.mulVec x i
  calc
    q * (∑ i, C z i * N.input.mulVec x i) =
        ∑ i, C z i * (q * N.input.mulVec x i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ ≤ ∑ i, C z i * N.output.mulVec x i := hsum

omit [Fintype ζ] in
theorem maf_le_aggregate_maf (C : Matrix ζ ι ℝ) (hC : Matrix.EntrywiseNonnegative C)
    (N : Network ι κ) {a b : ℝ} (ha : N.IsMAF a)
    (hb : (N.aggregate C).IsMAF b) : a ≤ b := by
  exact hb.2 a (feasibleAt_aggregate C hC N a ha.1)

omit [Fintype κ] in
theorem priceCone_aggregate_lift (C : Matrix ζ ι ℝ)
    (hC : Matrix.EntrywiseNonnegative C) (N : Network ι κ) (q : ℝ) (p : ζ → ℝ)
    (hp : p ∈ (N.aggregate C).priceCone q) :
    Matrix.vecMul p C ∈ N.priceCone q := by
  rcases hp with ⟨hpnonneg, hpstrict⟩
  refine ⟨?_, fun r => ?_⟩
  · intro i
    exact Finset.sum_nonneg fun z _ => mul_nonneg (hpnonneg z) (hC z i)
  · have hr := hpstrict r
    change Matrix.vecMul (Matrix.vecMul p C) N.output r <
      q * Matrix.vecMul (Matrix.vecMul p C) N.input r
    simpa [Network.aggregate, weightedColumn] using hr

omit [Fintype κ] in
theorem strictPriceAt_aggregate_implies (C : Matrix ζ ι ℝ)
    (hC : Matrix.EntrywiseNonnegative C) (N : Network ι κ) (q : ℝ) :
    (N.aggregate C).StrictPriceAt q → N.StrictPriceAt q := by
  intro h
  obtain ⟨p, hp⟩ := (strictPriceAt_iff_exists_obstruction (N.aggregate C) q).mp h
  exact (strictPriceAt_iff_exists_obstruction N q).mpr
    ⟨Matrix.vecMul p C, priceCone_aggregate_lift C hC N q p hp⟩

omit [Fintype κ] in
theorem priceCone_aggregate_iff (C : Matrix ζ ι ℝ)
    (hC : Matrix.EntrywiseNonnegative C) (N : Network ι κ) (q : ℝ) (p : ζ → ℝ) :
    p ∈ (N.aggregate C).priceCone q ↔
      (∀ z, 0 ≤ p z) ∧ Matrix.vecMul p C ∈ N.priceCone q := by
  constructor
  · intro hp
    exact ⟨hp.1, priceCone_aggregate_lift C hC N q p hp⟩
  · rintro ⟨hp, hlift⟩
    refine ⟨hp, fun r => ?_⟩
    have hr := hlift.2 r
    change Matrix.vecMul (Matrix.vecMul p C) N.output r <
      q * Matrix.vecMul (Matrix.vecMul p C) N.input r at hr
    change Matrix.vecMul p (C * N.output) r <
      q * Matrix.vecMul p (C * N.input) r
    simpa only [Matrix.vecMul_vecMul] using hr

omit [Fintype ζ] [Fintype κ] in
theorem inputNonnegative_aggregate (C : Matrix ζ ι ℝ)
    (hC : Matrix.EntrywiseNonnegative C) (N : Network ι κ)
    (hN : N.InputNonnegative) : (N.aggregate C).InputNonnegative := by
  intro z r
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hC z i) (hN i r)

theorem aggregate_isMAF_same_iff_liftedPricesAbove
    (C : Matrix ζ ι ℝ) (hC : Matrix.EntrywiseNonnegative C)
    (N : Network ι κ) (hN : N.InputNonnegative) {a : ℝ} (ha : N.IsMAF a) :
    (N.aggregate C).IsMAF a ↔
      ∀ q, a < q → ∃ p : ζ → ℝ,
        (∀ z, 0 ≤ p z) ∧ Matrix.vecMul p C ∈ N.priceCone q := by
  constructor
  · intro hagg q hq
    have hp := (hagg.lt_iff_strictPriceAt
      (inputNonnegative_aggregate C hC N hN) q).mp hq
    obtain ⟨p, hp⟩ := (strictPriceAt_iff_exists_obstruction (N.aggregate C) q).mp hp
    exact ⟨p, (priceCone_aggregate_iff C hC N q p).mp hp⟩
  · intro hprices
    constructor
    · exact feasibleAt_aggregate C hC N a ha.1
    · intro q hq
      by_contra hnot
      have hlt : a < q := lt_of_not_ge hnot
      obtain ⟨p, hp⟩ := hprices q hlt
      have hpagg : p ∈ (N.aggregate C).priceCone q :=
        (priceCone_aggregate_iff C hC N q p).mpr hp
      have hstrict : (N.aggregate C).StrictPriceAt q :=
        (strictPriceAt_iff_exists_obstruction (N.aggregate C) q).mpr ⟨p, hpagg⟩
      exact (feasibleAt_iff_not_strictPriceAt (N.aggregate C) q).mp hq hstrict

theorem aggregate_strictIncrease_iff_no_liftedPricesAbove
    (C : Matrix ζ ι ℝ) (hC : Matrix.EntrywiseNonnegative C)
    (N : Network ι κ) (hN : N.InputNonnegative)
    {a b : ℝ} (ha : N.IsMAF a) (hb : (N.aggregate C).IsMAF b) :
    a < b ↔
      ¬ ∀ q, a < q → ∃ p : ζ → ℝ,
        (∀ z, 0 ≤ p z) ∧ Matrix.vecMul p C ∈ N.priceCone q := by
  have hle : a ≤ b := maf_le_aggregate_maf C hC N ha hb
  rw [← aggregate_isMAF_same_iff_liftedPricesAbove C hC N hN ha]
  constructor
  · intro hlt heq
    have := hb.unique heq
    linarith
  · intro hne
    exact lt_of_le_of_ne hle fun heq => hne (heq ▸ hb)

end MAFComposition
