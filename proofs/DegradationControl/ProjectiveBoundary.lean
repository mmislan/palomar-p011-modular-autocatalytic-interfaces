import proofs.DegradationControl.Certificates

namespace DegradationControl

def NonnegativeVector (v : ι → ℝ) : Prop := ∀ i, 0 ≤ v i

def NormalizedPositive [Fintype ι] (v : ι → ℝ) : Prop :=
  StrictlyPositive v ∧ ∑ i, v i = 1

/-- Algebraic critical boundary.  For irreducible Metzler matrices, the
Perron theorem identifies this exactly with spectral bound zero. -/
def AlgebraicCritical [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) : Prop :=
  NonnegativeVector d ∧ ∃ v, NormalizedPositive v ∧
    Matrix.mulVec (degradedMatrix A d) v = 0

/-- The precise Perron uniqueness interface needed for projective
injectivity, separated from Mathlib's currently missing PF theorem. -/
def PositiveKernelRayUnique [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : Prop :=
  ∀ v w, StrictlyPositive v → StrictlyPositive w →
    Matrix.mulVec M v = 0 → Matrix.mulVec M w = 0 →
    ∃ c : ℝ, 0 < c ∧ w = c • v

theorem algebraicCritical_iff_projective [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) :
    AlgebraicCritical A d ↔
      ∃ v, NormalizedPositive v ∧
        NonnegativeVector (projectiveDegradation A v) ∧
        d = projectiveDegradation A v := by
  constructor
  · rintro ⟨hd, v, hv, hker⟩
    have hv0 : ∀ i, v i ≠ 0 := fun i => ne_of_gt (hv.1 i)
    have hrecover := critical_determines_degradation A d v hv0 hker
    refine ⟨v, hv, ?_, hrecover⟩
    intro i
    rw [← hrecover]
    exact hd i
  · rintro ⟨v, hv, hd, rfl⟩
    refine ⟨hd, v, hv, ?_⟩
    exact projectiveDegradation_is_critical A v (fun i => ne_of_gt (hv.1 i))

theorem normalized_projective_injective [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ)
    (huniq : ∀ d, PositiveKernelRayUnique (degradedMatrix A d))
    {v w : ι → ℝ} (hv : NormalizedPositive v)
    (hw : NormalizedPositive w)
    (hphi : projectiveDegradation A v = projectiveDegradation A w) :
    v = w := by
  have hv0 : ∀ i, v i ≠ 0 := fun i => ne_of_gt (hv.1 i)
  have hw0 : ∀ i, w i ≠ 0 := fun i => ne_of_gt (hw.1 i)
  have hvker := projectiveDegradation_is_critical A v hv0
  have hwker0 := projectiveDegradation_is_critical A w hw0
  have hwker :
      Matrix.mulVec (degradedMatrix A (projectiveDegradation A v)) w = 0 := by
    rw [hphi]
    exact hwker0
  obtain ⟨c, hc, hscale⟩ :=
    huniq (projectiveDegradation A v) v w hv.1 hw.1 hvker hwker
  have hsum := congrArg (fun z : ι → ℝ => ∑ i, z i) hscale
  have hc1 : c = 1 := by
    have hone_c : (1 : ℝ) = c := by
      calc
        1 = ∑ i, c * v i := by simpa [hw.2] using hsum
        _ = c * ∑ i, v i := by rw [Finset.mul_sum]
        _ = c := by rw [hv.2, mul_one]
    exact hone_c.symm
  rw [hc1] at hscale
  simpa using hscale.symm

end DegradationControl
