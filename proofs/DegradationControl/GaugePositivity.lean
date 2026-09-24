import proofs.DegradationControl.RobustInterval

namespace DegradationControl

/-- Positive time rescaling multiplies the projective critical degradation
profile by the same factor. -/
theorem projectiveDegradation_timeScale
    [Fintype ι] (A : Matrix ι ι ℝ) (v : ι → ℝ) (i : ι) (tau : ℝ) :
    projectiveDegradation (tau • A) v i = tau * projectiveDegradation A v i := by
  rw [projectiveDegradation, projectiveDegradation, Matrix.smul_mulVec]
  change tau * Matrix.mulVec A v i / v i = tau * (Matrix.mulVec A v i / v i)
  ring

/-- Tangent-cone condition behind positive-orthant invariance: at a zero
coordinate, an off-diagonal-nonnegative linear vector field points inward. -/
theorem mulVec_nonnegative_at_zero_coordinate
    [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} {v : ι → ℝ} {i : ι}
    (hM : ∀ p q, p ≠ q → 0 ≤ M p q)
    (hv : ∀ j, 0 ≤ v j) (hi : v i = 0) :
    0 ≤ Matrix.mulVec M v i := by
  apply Finset.sum_nonneg
  intro j hj
  by_cases hji : j = i
  · subst j
    simp [hi]
  · exact mul_nonneg (hM i j (Ne.symm hji)) (hv j)

end DegradationControl
