import proofs.DegradationControl.PartialActuation
import Mathlib.Analysis.MeanInequalities

namespace DegradationControl

/-- The diluted linearization of a directed three-cycle.  Each `aᵢ` is a
positive diagonal loss and the `bᵢ` are the three directed edge gains. -/
def threeCycleMatrix (a b : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-a 0, 0, b 2;
      b 0, -a 1, 0;
      0, b 1, -a 2]

/-- The zero-eigenvalue boundary of a three-cycle is the product balance
`a₀a₁a₂ = b₀b₁b₂`. -/
theorem threeCycleMatrix_det (a b : Fin 3 → ℝ) :
    Matrix.det (threeCycleMatrix a b) =
      -(a 0 * a 1 * a 2) + b 0 * b 1 * b 2 := by
  rw [Matrix.det_fin_three]
  simp [threeCycleMatrix]
  ring

/-- Three-variable AM--GM in the exact normalized form used by the
water-filling certificate. -/
theorem three_le_sum_of_one_le_product {r₀ r₁ r₂ : ℝ}
    (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (hprod : 1 ≤ r₀ * r₁ * r₂) :
    3 ≤ r₀ + r₁ + r₂ := by
  have hamgm := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (1 : ℝ) / 3) (w₂ := (1 : ℝ) / 3) (w₃ := (1 : ℝ) / 3)
    (p₁ := r₀) (p₂ := r₁) (p₃ := r₂)
    (by norm_num) (by norm_num) (by norm_num) hr₀ hr₁ hr₂ (by norm_num)
  have hroot : 1 ≤ (r₀ * r₁ * r₂) ^ ((1 : ℝ) / 3) := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hprod (by norm_num)
  rw [Real.mul_rpow (mul_nonneg hr₀ hr₁) hr₂,
    Real.mul_rpow hr₀ hr₁] at hroot
  nlinarith

/-- A finite, exact KKT/AM--GM certificate for a three-actuator water-fill.
`xᵢ` is the candidate denominator `kᵢ+dᵢ`; `yᵢ` is any feasible
competitor.  The complementarity inequalities are precisely the part of the
water-filling active-set conditions needed for the global certificate. -/
theorem threeCycle_waterfill_global
    {c₀ c₁ c₂ x₀ x₁ x₂ y₀ y₁ y₂ μ : ℝ}
    (hx₀ : 0 < x₀) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hy₀ : 0 ≤ y₀) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂)
    (hμ : 0 < μ)
    (hcomp₀ : (c₀ * x₀ - μ) * (y₀ / x₀ - 1) ≥ 0)
    (hcomp₁ : (c₁ * x₁ - μ) * (y₁ / x₁ - 1) ≥ 0)
    (hcomp₂ : (c₂ * x₂ - μ) * (y₂ / x₂ - 1) ≥ 0)
    (hprod : x₀ * x₁ * x₂ ≤ y₀ * y₁ * y₂) :
    c₀ * x₀ + c₁ * x₁ + c₂ * x₂ ≤
      c₀ * y₀ + c₁ * y₁ + c₂ * y₂ := by
  let r₀ := y₀ / x₀
  let r₁ := y₁ / x₁
  let r₂ := y₂ / x₂
  have hr₀ : 0 ≤ r₀ := div_nonneg hy₀ hx₀.le
  have hr₁ : 0 ≤ r₁ := div_nonneg hy₁ hx₁.le
  have hr₂ : 0 ≤ r₂ := div_nonneg hy₂ hx₂.le
  have hratio : 1 ≤ r₀ * r₁ * r₂ := by
    dsimp [r₀, r₁, r₂]
    rw [div_mul_div_comm, div_mul_div_comm]
    exact (le_div_iff₀ (mul_pos (mul_pos hx₀ hx₁) hx₂)).2 (by
      simpa [mul_assoc] using hprod)
  have hsum := three_le_sum_of_one_le_product hr₀ hr₁ hr₂ hratio
  have hyx₀ : y₀ = x₀ * r₀ := by
    dsimp [r₀]
    calc
      y₀ = y₀ / x₀ * x₀ := (div_mul_cancel₀ y₀ hx₀.ne').symm
      _ = x₀ * (y₀ / x₀) := by ring
  have hyx₁ : y₁ = x₁ * r₁ := by
    dsimp [r₁]
    calc
      y₁ = y₁ / x₁ * x₁ := (div_mul_cancel₀ y₁ hx₁.ne').symm
      _ = x₁ * (y₁ / x₁) := by ring
  have hyx₂ : y₂ = x₂ * r₂ := by
    dsimp [r₂]
    calc
      y₂ = y₂ / x₂ * x₂ := (div_mul_cancel₀ y₂ hx₂.ne').symm
      _ = x₂ * (y₂ / x₂) := by ring
  change 0 ≤ (c₀ * x₀ - μ) * (r₀ - 1) at hcomp₀
  change 0 ≤ (c₁ * x₁ - μ) * (r₁ - 1) at hcomp₁
  change 0 ≤ (c₂ * x₂ - μ) * (r₂ - 1) at hcomp₂
  rw [hyx₀, hyx₁, hyx₂]
  nlinarith

end DegradationControl
