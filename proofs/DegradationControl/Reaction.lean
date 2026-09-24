import Mathlib

namespace DegradationControl

/-- A diluted one-reactant reaction. `products i` is the stoichiometric
coefficient of species `i`; chemostatted species are not indexed here. -/
structure UnaryReaction (ι : Type*) where
  substrate : ι
  products : ι → ℝ
  rate : ℝ

/-- Column-convention contribution of `X_substrate -> sum_i products i * X_i`.
The source species is consumed once. -/
def UnaryReaction.matrix [DecidableEq ι] (r : UnaryReaction ι) : Matrix ι ι ℝ :=
  fun i j => if j = r.substrate then
    r.rate * (r.products i - if i = r.substrate then 1 else 0)
  else 0

/-- Static species-wise degradation is a negative diagonal matrix. -/
def degradationMatrix [DecidableEq ι] (d : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => if i = j then -d i else 0

theorem degradationMatrix_apply [DecidableEq ι] (d : ι → ℝ) (i j : ι) :
    degradationMatrix d i j = if i = j then -d i else 0 := by
  rfl

theorem UnaryReaction.matrix_offDiag_nonneg [DecidableEq ι]
    (r : UnaryReaction ι) (hrate : 0 ≤ r.rate)
    (hprod : ∀ i, 0 ≤ r.products i) {i j : ι} (hij : i ≠ j) :
    0 ≤ r.matrix i j := by
  by_cases hj : j = r.substrate
  · have hi : i ≠ r.substrate := by
      intro his
      apply hij
      calc
        i = r.substrate := his
        _ = j := hj.symm
    simp [UnaryReaction.matrix, hj, hi, mul_nonneg hrate (hprod i)]
  · simp [UnaryReaction.matrix, hj]

theorem UnaryReaction.matrix_substrate_column [DecidableEq ι]
    (r : UnaryReaction ι) (i : ι) :
    r.matrix i r.substrate =
      r.rate * (r.products i - if i = r.substrate then 1 else 0) := by
  simp [UnaryReaction.matrix]

theorem UnaryReaction.matrix_other_column [DecidableEq ι]
    (r : UnaryReaction ι) {j : ι} (hj : j ≠ r.substrate) (i : ι) :
    r.matrix i j = 0 := by
  simp [UnaryReaction.matrix, hj]

end DegradationControl
