import Mathlib
import proofs.MAFComposition.Composition

/-!
Disjoint species-and-reaction union.  Unlike shared-species parallel union,
this block-diagonal operation has an exact maximum law for attained MAFs.
-/

namespace MAFComposition

variable {ι ζ κ ρ : Type}
  [Fintype ι] [Fintype ζ] [Fintype κ] [Fintype ρ]

def blockColumns (M₁ : Matrix ι κ ℝ) (M₂ : Matrix ζ ρ ℝ) :
    Matrix (Sum ι ζ) (Sum κ ρ) ℝ
  | Sum.inl i, Sum.inl r => M₁ i r
  | Sum.inr z, Sum.inr s => M₂ z s
  | _, _ => 0

def Network.directSum (N₁ : Network ι κ) (N₂ : Network ζ ρ) :
    Network (Sum ι ζ) (Sum κ ρ) where
  input := blockColumns N₁.input N₂.input
  output := blockColumns N₁.output N₂.output

omit [Fintype ι] [Fintype ζ] in
theorem feasibleAt_directSum_of_left (N₁ : Network ι κ) (N₂ : Network ζ ρ)
    (q : ℝ) (h : N₁.FeasibleAt q) : (N₁.directSum N₂).FeasibleAt q := by
  rcases h with ⟨x, hx, hxne, hineq⟩
  let y : Sum κ ρ → ℝ := Sum.elim x (fun _ => 0)
  refine ⟨y, ?_, ?_, ?_⟩
  · intro r
    cases r with
    | inl r => exact hx r
    | inr _ => exact le_rfl
  · intro hy
    apply hxne
    funext r
    have := congrFun hy (Sum.inl r)
    exact this
  · intro s
    cases s with
    | inl i => simpa [Network.directSum, blockColumns, Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type, y] using hineq i
    | inr z => simp [Network.directSum, blockColumns, Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type, y]

omit [Fintype ι] [Fintype ζ] in
theorem feasibleAt_directSum_of_right (N₁ : Network ι κ) (N₂ : Network ζ ρ)
    (q : ℝ) (h : N₂.FeasibleAt q) : (N₁.directSum N₂).FeasibleAt q := by
  rcases h with ⟨x, hx, hxne, hineq⟩
  let y : Sum κ ρ → ℝ := Sum.elim (fun _ => 0) x
  refine ⟨y, ?_, ?_, ?_⟩
  · intro r
    cases r with
    | inl _ => exact le_rfl
    | inr r => exact hx r
  · intro hy
    apply hxne
    funext r
    have := congrFun hy (Sum.inr r)
    exact this
  · intro s
    cases s with
    | inl i => simp [Network.directSum, blockColumns, Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type, y]
    | inr z => simpa [Network.directSum, blockColumns, Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type, y] using hineq z

omit [Fintype κ] [Fintype ρ] in
theorem strictPriceAt_directSum (N₁ : Network ι κ) (N₂ : Network ζ ρ) (q : ℝ)
    (h₁ : N₁.StrictPriceAt q) (h₂ : N₂.StrictPriceAt q) :
    (N₁.directSum N₂).StrictPriceAt q := by
  obtain ⟨p₁, hp₁, hs₁⟩ := (strictPriceAt_iff_exists_obstruction N₁ q).mp h₁
  obtain ⟨p₂, hp₂, hs₂⟩ := (strictPriceAt_iff_exists_obstruction N₂ q).mp h₂
  apply (strictPriceAt_iff_exists_obstruction (N₁.directSum N₂) q).mpr
  let p : Sum ι ζ → ℝ := Sum.elim p₁ p₂
  refine ⟨p, ?_, ?_⟩
  · intro s
    cases s with
    | inl i => exact hp₁ i
    | inr z => exact hp₂ z
  · intro r
    cases r with
    | inl r => simpa [Network.directSum, blockColumns, weightedColumn, p] using hs₁ r
    | inr r => simpa [Network.directSum, blockColumns, weightedColumn, p] using hs₂ r

theorem directSum_isMAF_max (N₁ : Network ι κ) (N₂ : Network ζ ρ)
    (hA₁ : N₁.InputNonnegative) (hA₂ : N₂.InputNonnegative)
    {a b : ℝ} (ha : N₁.IsMAF a) (hb : N₂.IsMAF b) :
    (N₁.directSum N₂).IsMAF (max a b) := by
  constructor
  · rcases le_total a b with hab | hba
    · exact feasibleAt_directSum_of_right N₁ N₂ (max a b) <|
        by simpa [max_eq_right hab] using hb.1
    · exact feasibleAt_directSum_of_left N₁ N₂ (max a b) <|
        by simpa [max_eq_left hba] using ha.1
  · intro q hq
    by_contra hnot
    have hmaxq : max a b < q := lt_of_not_ge hnot
    have ha_q : a < q := lt_of_le_of_lt (le_max_left a b) hmaxq
    have hb_q : b < q := lt_of_le_of_lt (le_max_right a b) hmaxq
    have hp₁ := (ha.lt_iff_strictPriceAt hA₁ q).mp ha_q
    have hp₂ := (hb.lt_iff_strictPriceAt hA₂ q).mp hb_q
    have hp := strictPriceAt_directSum N₁ N₂ q hp₁ hp₂
    exact (feasibleAt_iff_not_strictPriceAt (N₁.directSum N₂) q).mp hq hp

end MAFComposition
