import proofs.DegradationControl.CycleControl

namespace DegradationControl

/-- Smallest nondegenerate diluted Type II_1 core: the first reaction splits
to the next species with gain `p` and back to the third species with gain `q`.
The remaining reactions close the base cycle. -/
def typeII1Matrix (a b c p q r u : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-a, 0, r;
      p, -b, 0;
      q, u, -c]

/-- Cycle-cover compression of the first overlapping core.  The two positive
terms are exactly the short and long cycle covers. -/
theorem typeII1Matrix_det (a b c p q r u : ℝ) :
    Matrix.det (typeII1Matrix a b c p q r u) =
      -(a * b * c) + b * q * r + p * r * u := by
  rw [Matrix.det_fin_three]
  simp [typeII1Matrix]
  ring

/-- At zero eigenvalue, the determinant identity is exactly the sum of the
two normalized cycle gains. -/
theorem typeII1_boundary_iff_gain_sum
    {a b c p q r u : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Matrix.det (typeII1Matrix a b c p q r u) = 0 ↔
      r * q / (a * c) + r * p * u / (a * b * c) = 1 := by
  rw [typeII1Matrix_det]
  field_simp [ha, hb, hc]
  constructor <;> intro h <;> nlinarith

/-- Physical-branch selector.  If `t>0` solves the Perron equation of the
normalized Type II_1 next-generation matrix, then it crosses one exactly when
the sum of the short and long normalized cycle gains crosses one. -/
theorem typeII1_perron_gt_one_iff
    {t gShort gLong : ℝ} (ht : 0 < t) (hgLong : 0 < gLong)
    (hroot : t ^ 3 = gShort * t + gLong) :
    1 < t ↔ 1 < gShort + gLong := by
  have hmul : gShort * t < t ^ 2 * t := by
    have : gShort * t < t ^ 3 := by nlinarith
    simpa [pow_succ] using this
  have hgShort : gShort < t ^ 2 := lt_of_mul_lt_mul_right hmul ht.le
  have hfactor : 0 < t ^ 2 + t + 1 - gShort := by nlinarith
  have hid : gShort + gLong - 1 =
      (t - 1) * (t ^ 2 + t + 1 - gShort) := by
    calc
      gShort + gLong - 1 = gShort + (t ^ 3 - gShort * t) - 1 := by
        rw [hroot]
        ring
      _ = (t - 1) * (t ^ 2 + t + 1 - gShort) := by ring
  constructor <;> intro h
  · have : 0 < (t - 1) * (t ^ 2 + t + 1 - gShort) :=
      mul_pos (by linarith) hfactor
    nlinarith
  · have : 0 < (t - 1) * (t ^ 2 + t + 1 - gShort) := by
      nlinarith
    have : 0 < t - 1 := pos_of_mul_pos_left this hfactor.le
    linarith

theorem typeII1_perron_eq_one_iff
    {t gShort gLong : ℝ} (ht : 0 < t) (hgLong : 0 < gLong)
    (hroot : t ^ 3 = gShort * t + gLong) :
    t = 1 ↔ gShort + gLong = 1 := by
  have hmul : gShort * t < t ^ 2 * t := by
    have : gShort * t < t ^ 3 := by nlinarith
    simpa [pow_succ] using this
  have hgShort : gShort < t ^ 2 := lt_of_mul_lt_mul_right hmul ht.le
  have hfactor : 0 < t ^ 2 + t + 1 - gShort := by nlinarith
  have hid : gShort + gLong - 1 =
      (t - 1) * (t ^ 2 + t + 1 - gShort) := by
    calc
      gShort + gLong - 1 = gShort + (t ^ 3 - gShort * t) - 1 := by
        rw [hroot]
        ring
      _ = (t - 1) * (t ^ 2 + t + 1 - gShort) := by ring
  constructor
  · intro h
    subst t
    norm_num at hroot ⊢
    linarith
  · intro h
    have : (t - 1) * (t ^ 2 + t + 1 - gShort) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with hleft | hright
    · exact sub_eq_zero.mp hleft
    · exact False.elim ((ne_of_gt hfactor) hright)

end DegradationControl
