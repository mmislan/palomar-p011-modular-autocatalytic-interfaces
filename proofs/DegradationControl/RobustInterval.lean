import proofs.DegradationControl.SCCAssembly

namespace DegradationControl

/-- Multiplication by a componentwise nonnegative vector preserves entrywise
matrix order. -/
theorem mulVec_le_mulVec_of_entrywise_le
    [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} {v : ι → ℝ}
    (hAB : ∀ i j, A i j ≤ B i j) (hv : ∀ j, 0 ≤ v j) :
    ∀ i, Matrix.mulVec A v i ≤ Matrix.mulVec B v i := by
  intro i
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hAB i j) (hv j)

/-- Robust suppression certificate.  The largest source-gain / smallest
degradation corner supplies one common strict extinction witness for the whole
independent interval family. -/
theorem upperCorner_extinction_common
    [Fintype ι] [DecidableEq ι]
    {B Bupper : Matrix ι ι ℝ} {d dlower v : ι → ℝ}
    (hB : ∀ i j, B i j ≤ Bupper i j)
    (hd : ∀ i, dlower i ≤ d i)
    (hv : ∀ i, 0 ≤ v i)
    (hcorner : StrictlyNegative (Matrix.mulVec (degradedMatrix Bupper dlower) v)) :
    StrictlyNegative (Matrix.mulVec (degradedMatrix B d) v) := by
  intro i
  rw [degraded_mulVec_apply]
  have hcorner_i := hcorner i
  rw [degraded_mulVec_apply] at hcorner_i
  have hmul := mulVec_le_mulVec_of_entrywise_le hB hv i
  have hdeg : dlower i * v i ≤ d i * v i :=
    mul_le_mul_of_nonneg_right (hd i) (hv i)
  exact lt_of_le_of_lt (by linarith) hcorner_i

/-- Robust guaranteed-growth certificate at the smallest source-gain /
largest degradation corner. -/
theorem lowerCorner_growth_common
    [Fintype ι] [DecidableEq ι]
    {Blower B : Matrix ι ι ℝ} {d dupper v : ι → ℝ}
    (hB : ∀ i j, Blower i j ≤ B i j)
    (hd : ∀ i, d i ≤ dupper i)
    (hv : ∀ i, 0 ≤ v i)
    (hcorner : StrictlyPositive (Matrix.mulVec (degradedMatrix Blower dupper) v)) :
    StrictlyPositive (Matrix.mulVec (degradedMatrix B d) v) := by
  intro i
  rw [degraded_mulVec_apply]
  have hcorner_i := hcorner i
  rw [degraded_mulVec_apply] at hcorner_i
  have hmul := mulVec_le_mulVec_of_entrywise_le hB hv i
  have hdeg : d i * v i ≤ dupper i * v i :=
    mul_le_mul_of_nonneg_right (hd i) (hv i)
  exact lt_of_lt_of_le hcorner_i (by linarith)

end DegradationControl
