import proofs.DegradationControl.TypeII

namespace DegradationControl

/-- Cycle-cover polynomial for the minimal Type II_2 core after setting
`z=t²`.  The short-cycle gains are `g₁,g₂` and `gLong` is the base-cycle
gain. -/
def typeII2PerronPolynomial (g₁ g₂ gLong z : ℝ) : ℝ :=
  (z - g₁) * (z - g₂) - gLong

/-- Exact physical-branch selector for Type II_2.  The hypotheses `gᵢ<z`
identify the larger (Perron) root of the quadratic in `z=t²`. -/
theorem typeII2_perron_lt_one_iff
    {g₁ g₂ gLong z : ℝ}
    (hg₁z : g₁ < z) (hg₂z : g₂ < z)
    (hroot : (z - g₁) * (z - g₂) = gLong) :
    z < 1 ↔
      g₁ < 1 ∧ g₂ < 1 ∧ gLong < (1 - g₁) * (1 - g₂) := by
  constructor
  · intro hz
    have h₁ : g₁ < 1 := lt_trans hg₁z hz
    have h₂ : g₂ < 1 := lt_trans hg₂z hz
    have hfirst : (z - g₁) * (z - g₂) < (1 - g₁) * (z - g₂) :=
      mul_lt_mul_of_pos_right (by linarith) (by linarith)
    have hsecond : (1 - g₁) * (z - g₂) < (1 - g₁) * (1 - g₂) :=
      mul_lt_mul_of_pos_left (by linarith) (by linarith)
    exact ⟨h₁, h₂, by rw [← hroot]; exact lt_trans hfirst hsecond⟩
  · rintro ⟨h₁, h₂, hgain⟩
    by_contra hn
    have hz : 1 ≤ z := le_of_not_gt hn
    have hprod : (1 - g₁) * (1 - g₂) ≤ (z - g₁) * (z - g₂) := by
      exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    rw [hroot] at hprod
    linarith

theorem typeII2_perron_eq_one_iff
    {g₁ g₂ gLong z : ℝ}
    (hg₁z : g₁ < z) (hg₂z : g₂ < z)
    (hroot : (z - g₁) * (z - g₂) = gLong) :
    z = 1 ↔ g₁ < 1 ∧ g₂ < 1 ∧ gLong = (1 - g₁) * (1 - g₂) := by
  constructor
  · intro hz
    subst z
    exact ⟨hg₁z, hg₂z, hroot.symm⟩
  · rintro ⟨h₁, h₂, hgain⟩
    have hpos₁ : 0 < z - g₁ := by linarith
    have hpos₂ : 0 < z - g₂ := by linarith
    have hid : (z - g₁) * (z - g₂) = (1 - g₁) * (1 - g₂) := by
      rw [hroot, hgain]
    by_contra hz
    rcases lt_or_gt_of_ne hz with hzlt | hzgt
    · have hfirst : (z - g₁) * (z - g₂) < (1 - g₁) * (z - g₂) :=
        mul_lt_mul_of_pos_right (by linarith) hpos₂
      have hsecond : (1 - g₁) * (z - g₂) < (1 - g₁) * (1 - g₂) :=
        mul_lt_mul_of_pos_left (by linarith) (by linarith)
      linarith
    · have hfirst : (1 - g₁) * (1 - g₂) < (z - g₁) * (1 - g₂) :=
        mul_lt_mul_of_pos_right (by linarith) (by linarith)
      have hsecond : (z - g₁) * (1 - g₂) < (z - g₁) * (z - g₂) :=
        mul_lt_mul_of_pos_left (by linarith) hpos₁
      linarith

/-- Exact witness that determinant zero does not select the Perron branch:
both `z=1` and `z=4` solve the same positive-gain Type II_2 equation. -/
theorem typeII2_nonphysical_branch_witness :
    typeII2PerronPolynomial 2 3 2 1 = 0 ∧
      typeII2PerronPolynomial 2 3 2 4 = 0 := by
  norm_num [typeII2PerronPolynomial]

end DegradationControl
