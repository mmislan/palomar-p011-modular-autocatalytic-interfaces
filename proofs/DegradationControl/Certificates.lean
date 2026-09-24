import proofs.DegradationControl.Network

namespace DegradationControl

def StrictlyPositive (v : ι → ℝ) : Prop := ∀ i, 0 < v i

def StrictlyNegative (v : ι → ℝ) : Prop := ∀ i, v i < 0

def GrowthCertificate [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) : Prop :=
  ∃ v, StrictlyPositive v ∧ StrictlyPositive (Matrix.mulVec M v)

def CriticalCertificate [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) : Prop :=
  ∃ v, StrictlyPositive v ∧ Matrix.mulVec M v = 0

def ExtinctionCertificate [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) : Prop :=
  ∃ v, StrictlyPositive v ∧ StrictlyNegative (Matrix.mulVec M v)

/-- The abstract Metzler matrix `A` after species-wise degradation `d`. -/
def degradedMatrix [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) : Matrix ι ι ℝ :=
  A + degradationMatrix d

theorem degraded_mulVec_apply [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d v : ι → ℝ) (i : ι) :
    Matrix.mulVec (degradedMatrix A d) v i =
      Matrix.mulVec A v i - d i * v i := by
  have hdeg : degradationMatrix d = -Matrix.diagonal d := by
    ext p q
    by_cases hpq : p = q <;> simp [degradationMatrix, Matrix.diagonal, hpq]
  rw [degradedMatrix, Matrix.add_mulVec]
  change Matrix.mulVec A v i + Matrix.mulVec (degradationMatrix d) v i = _
  rw [hdeg, Matrix.neg_mulVec]
  simp [Matrix.mulVec_diagonal]
  ring

/-- Projective positive-composition degradation profile `Av/v`. -/
noncomputable def projectiveDegradation [Fintype ι]
    (A : Matrix ι ι ℝ) (v : ι → ℝ) (i : ι) : ℝ :=
  Matrix.mulVec A v i / v i

theorem projectiveDegradation_is_critical [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (v : ι → ℝ) (hv : ∀ i, v i ≠ 0) :
    Matrix.mulVec (degradedMatrix A (projectiveDegradation A v)) v = 0 := by
  ext i
  rw [degraded_mulVec_apply]
  simp [projectiveDegradation, hv i]

theorem critical_determines_degradation [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d v : ι → ℝ) (hv : ∀ i, v i ≠ 0)
    (hcrit : Matrix.mulVec (degradedMatrix A d) v = 0) :
    d = projectiveDegradation A v := by
  funext i
  have hi : Matrix.mulVec A v i - d i * v i = 0 := by
    simpa [degraded_mulVec_apply] using congrFun hcrit i
  apply (eq_div_iff (hv i)).2
  linarith

/-- Strict growth of a diagonally degraded system is exactly a projective
coordinatewise upper bound on the degradation vector. -/
theorem growthCertificate_degraded_iff_projective_lt
    [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) :
    GrowthCertificate (degradedMatrix A d) ↔
      ∃ v, StrictlyPositive v ∧
        ∀ i, d i < projectiveDegradation A v i := by
  constructor
  · rintro ⟨v, hv, hMv⟩
    refine ⟨v, hv, ?_⟩
    intro i
    apply (lt_div_iff₀ (hv i)).2
    have hi := hMv i
    rw [degraded_mulVec_apply] at hi
    linarith
  · rintro ⟨v, hv, hd⟩
    refine ⟨v, hv, ?_⟩
    intro i
    rw [degraded_mulVec_apply]
    have hi := (lt_div_iff₀ (hv i)).1 (hd i)
    linarith

/-- Criticality is exactly equality with the projective degradation profile. -/
theorem criticalCertificate_degraded_iff_projective_eq
    [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) :
    CriticalCertificate (degradedMatrix A d) ↔
      ∃ v, StrictlyPositive v ∧ d = projectiveDegradation A v := by
  constructor
  · rintro ⟨v, hv, hcrit⟩
    exact ⟨v, hv, critical_determines_degradation A d v
      (fun i ↦ ne_of_gt (hv i)) hcrit⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, projectiveDegradation_is_critical A v
      (fun i ↦ ne_of_gt (hv i))⟩

/-- Strict extinction of a diagonally degraded system is exactly a projective
coordinatewise lower bound on the degradation vector. -/
theorem extinctionCertificate_degraded_iff_projective_gt
    [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) :
    ExtinctionCertificate (degradedMatrix A d) ↔
      ∃ v, StrictlyPositive v ∧
        ∀ i, projectiveDegradation A v i < d i := by
  constructor
  · rintro ⟨v, hv, hMv⟩
    refine ⟨v, hv, ?_⟩
    intro i
    apply (div_lt_iff₀ (hv i)).2
    have hi := hMv i
    rw [degraded_mulVec_apply] at hi
    linarith
  · rintro ⟨v, hv, hd⟩
    refine ⟨v, hv, ?_⟩
    intro i
    rw [degraded_mulVec_apply]
    have hi := (div_lt_iff₀ (hv i)).1 (hd i)
    linarith

/-- Row-scaled next-generation action.  This fixes the convention as
`H⁻¹ B`: consumption is divided from the output (row) coordinate. -/
noncomputable def nextGenerationAction [Fintype ι]
    (h : ι → ℝ) (B : Matrix ι ι ℝ) (v : ι → ℝ) (i : ι) : ℝ :=
  Matrix.mulVec B v i / h i

theorem nextGeneration_fixed_iff_kernel [Fintype ι] [DecidableEq ι]
    (h : ι → ℝ) (B : Matrix ι ι ℝ) (v : ι → ℝ)
    (hh : ∀ i, h i ≠ 0) :
    Matrix.mulVec (degradedMatrix B h) v = 0 ↔
      ∀ i, nextGenerationAction h B v i = v i := by
  constructor
  · intro hker i
    have hi : Matrix.mulVec B v i - h i * v i = 0 := by
      simpa [degraded_mulVec_apply] using congrFun hker i
    apply (div_eq_iff (hh i)).2
    calc
      Matrix.mulVec B v i = h i * v i := by linarith
      _ = v i * h i := mul_comm _ _
  · intro hfix
    ext i
    rw [degraded_mulVec_apply]
    have hi := hfix i
    dsimp [nextGenerationAction] at hi
    have hmul : Matrix.mulVec B v i = v i * h i :=
      (div_eq_iff (hh i)).1 hi
    calc
      Matrix.mulVec B v i - h i * v i =
          v i * h i - h i * v i := by rw [hmul]
      _ = 0 := by ring

end DegradationControl
