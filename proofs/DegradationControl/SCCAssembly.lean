import proofs.DegradationControl.FiniteAtlas

namespace DegradationControl

/-- Two one-species SCCs with a directed edge from the first (source) block to
the second block. -/
def twoBlockMatrix (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, 0; c, b]

theorem twoBlock_mulVec (a b c x y : ℝ) :
    Matrix.mulVec (twoBlockMatrix a b c) ![x, y] = ![a * x, c * x + b * y] := by
  ext i
  fin_cases i <;> simp [twoBlockMatrix, Matrix.mulVec]

/-- Exact smallest SCC discriminator.  With a positive edge from source block
to downstream block, a strictly positive all-coordinate growth certificate
exists iff the source block itself is supercritical; the downstream diagonal
`b` may have either sign. -/
theorem twoBlock_strictGrowth_iff_source_positive
    {a b c : ℝ} (hc : 0 < c) :
    (∃ x y : ℝ, 0 < x ∧ 0 < y ∧ 0 < a * x ∧ 0 < c * x + b * y) ↔
      0 < a := by
  constructor
  · rintro ⟨x, y, hx, hy, hax, hout⟩
    exact pos_of_mul_pos_left hax hx.le
  · intro ha
    by_cases hb : 0 ≤ b
    · exact ⟨1, 1, by norm_num, by norm_num, by simpa using ha,
        by simpa using add_pos_of_pos_of_nonneg hc hb⟩
    · have hbneg : b < 0 := lt_of_not_ge hb
      have hb0 : b ≠ 0 := ne_of_lt hbneg
      let y := (-c / b) / 2
      have hy0 : 0 < -c / b := div_pos_of_neg_of_neg (neg_neg_of_pos hc) hbneg
      have hy : 0 < y := by dsimp [y]; positivity
      have hout : 0 < c + b * y := by
        have heq : c + b * y = c / 2 := by
          dsimp [y]
          field_simp [hb0]
          ring
        rw [heq]
        positivity
      exact ⟨1, y, by norm_num, hy, by simpa using ha, by simpa using hout⟩

/-- A downstream growing block does not imply a global strict certificate if
the source block is stable. -/
theorem downstream_growth_not_global :
    ¬ (∃ x y : ℝ, 0 < x ∧ 0 < y ∧
      0 < (-1 : ℝ) * x ∧ 0 < 2 * x + 1 * y) := by
  rintro ⟨x, y, hx, hy, hsource, hdown⟩
  nlinarith

/-- A marginal source block yields weak nondecay but still cannot yield a
strict global certificate. -/
theorem marginal_source_not_strict_global :
    ¬ (∃ x y : ℝ, 0 < x ∧ 0 < y ∧
      0 < (0 : ℝ) * x ∧ 0 < 2 * x - y) := by
  simp

end DegradationControl
