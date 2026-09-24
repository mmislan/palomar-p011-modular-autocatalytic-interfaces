import proofs.DegradationControl.ProjectiveBoundary
import Mathlib.LinearAlgebra.Matrix.Gershgorin

namespace DegradationControl

open scoped ComplexConjugate

/-- Off-diagonal nonnegativity, the order property of a real Metzler matrix. -/
def IsMetzler [DecidableEq ι] (M : Matrix ι ι ℝ) : Prop :=
  ∀ i j, i ≠ j → 0 ≤ M i j

/-- Entrywise complexification of a real matrix. -/
def complexify (M : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  M.map Complex.ofReal

/-- `λ` is a real eigenvalue of `M` which dominates the real parts of all
complex eigenvalues.  This is the exact finite-dimensional spectral-bound
interface needed by the onset theorem. -/
def IsRealSpectralBound [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (lam : ℝ) : Prop :=
  Module.End.HasEigenvalue (Matrix.toLin' (complexify M)) (lam : ℂ) ∧
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (complexify M)) μ → μ.re ≤ lam

/-- Diagonal similarity by a positive weight vector. -/
noncomputable def weightedConjugate (M : Matrix ι ι ℝ) (v : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => (v i)⁻¹ * M i j * v j

theorem weightedConjugate_diag {M : Matrix ι ι ℝ} {v : ι → ℝ}
    (hv : StrictlyPositive v) (i : ι) :
    weightedConjugate M v i i = M i i := by
  dsimp [weightedConjugate]
  field_simp [ne_of_gt (hv i)]

theorem weightedConjugate_offDiag_nonneg [DecidableEq ι]
    {M : Matrix ι ι ℝ} {v : ι → ℝ}
    (hM : IsMetzler M) (hv : StrictlyPositive v)
    {i j : ι} (hij : i ≠ j) :
    0 ≤ weightedConjugate M v i j := by
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (le_of_lt (hv i))) (hM i j hij))
    (le_of_lt (hv j))

theorem weightedConjugate_rowSum [Fintype ι]
    {M : Matrix ι ι ℝ} {v : ι → ℝ} {lam : ℝ}
    (hv : StrictlyPositive v) (hMv : M.mulVec v = lam • v) (i : ι) :
    ∑ j, weightedConjugate M v i j = lam := by
  have hi := congrFun hMv i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi
  simp only [weightedConjugate, mul_assoc]
  rw [← Finset.mul_sum, hi]
  field_simp [ne_of_gt (hv i)]

theorem weightedConjugate_hasEigenvalue [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} {v : ι → ℝ} (hv : StrictlyPositive v) {mu : ℂ}
    (hmu : Module.End.HasEigenvalue (Matrix.toLin' (complexify M)) mu) :
    Module.End.HasEigenvalue
      (Matrix.toLin' (complexify (weightedConjugate M v))) mu := by
  obtain ⟨z, hz⟩ := hmu.exists_hasEigenvector
  let w : ι → ℂ := fun i => (v i : ℂ)⁻¹ * z i
  have hw_ne : w ≠ 0 := by
    intro hw
    apply hz.2
    funext i
    have hwi := congrFun hw i
    simp only [w, Pi.zero_apply] at hwi
    have hvi : (v i : ℂ)⁻¹ ≠ 0 :=
      inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (hv i)))
    exact (mul_eq_zero.mp hwi).resolve_left hvi
  apply Module.End.hasEigenvalue_of_hasEigenvector
  refine ⟨?_, hw_ne⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  ext i
  have hi := congrFun hz.apply_eq_smul i
  simp only [Matrix.toLin'_apply, complexify, Matrix.map_apply, Matrix.mulVec,
    dotProduct, Pi.smul_apply, smul_eq_mul] at hi ⊢
  change (∑ j, (((v i)⁻¹ * M i j * v j : ℝ) : ℂ) * ((v j : ℂ)⁻¹ * z j)) =
    mu * ((v i : ℂ)⁻¹ * z i)
  calc
    _ = (v i : ℂ)⁻¹ * ∑ j, (M i j : ℂ) * z j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      field_simp [ne_of_gt (hv i), ne_of_gt (hv j)]
    _ = mu * ((v i : ℂ)⁻¹ * z i) := by rw [hi]; ring

theorem realEigenvector_hasEigenvalue [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {M : Matrix ι ι ℝ} {v : ι → ℝ} {lam : ℝ}
    (hv : StrictlyPositive v) (hMv : M.mulVec v = lam • v) :
    Module.End.HasEigenvalue (Matrix.toLin' (complexify M)) (lam : ℂ) := by
  let vc : ι → ℂ := fun i => v i
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := vc) ?_
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    ext i
    have hi := congrFun hMv i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi
    simp only [complexify, Matrix.map_apply, Matrix.mulVec, dotProduct,
      Pi.smul_apply, smul_eq_mul, vc]
    simp_rw [← Complex.ofReal_mul]
    rw [← Complex.ofReal_sum, hi]
  · intro hvc
    have hi := congrFun hvc (Classical.arbitrary ι)
    change (v (Classical.arbitrary ι) : ℂ) = 0 at hi
    exact (Complex.ofReal_ne_zero.mpr (ne_of_gt (hv _))) hi

/-- Weighted Gershgorin spectral theorem. A positive real eigenvector of a
Metzler matrix identifies its eigenvalue with the spectral bound: every
complex eigenvalue has real part at most that value. -/
theorem positiveEigenvector_isRealSpectralBound
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {M : Matrix ι ι ℝ} {v : ι → ℝ} {lam : ℝ}
    (hM : IsMetzler M) (hv : StrictlyPositive v)
    (hMv : M.mulVec v = lam • v) :
    IsRealSpectralBound M lam := by
  refine ⟨realEigenvector_hasEigenvalue hv hMv, ?_⟩
  intro mu hmu
  let B := weightedConjugate M v
  have hBmu : Module.End.HasEigenvalue (Matrix.toLin' (complexify B)) mu :=
    weightedConjugate_hasEigenvalue hv hmu
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hBmu
  have hball :
      ‖(B k k : ℂ) - mu‖ ≤
        ∑ j ∈ Finset.univ.erase k, ‖(B k j : ℂ)‖ := by
    simpa only [mem_closedBall_iff_norm', complexify, Matrix.map_apply] using hk
  have hsum :
      ∑ j ∈ Finset.univ.erase k, ‖(B k j : ℂ)‖ = lam - B k k := by
    calc
      _ = ∑ j ∈ Finset.univ.erase k, B k j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        exact weightedConjugate_offDiag_nonneg hM hv (Finset.ne_of_mem_erase hj).symm
      _ = (∑ j, B k j) - B k k := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ k)]
      _ = lam - B k k := by
        rw [weightedConjugate_rowSum hv hMv]
  have hre := Complex.re_le_norm (mu - (B k k : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  have hnorm : ‖mu - (B k k : ℂ)‖ = ‖(B k k : ℂ) - mu‖ := by
    rw [← norm_neg]
    congr 1
    ring
  rw [hnorm] at hre
  rw [hsum] at hball
  exact (sub_le_sub_iff_right (B k k)).mp (hre.trans hball)

theorem degradedMatrix_isMetzler [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : IsMetzler A) (d : ι → ℝ) :
    IsMetzler (degradedMatrix A d) := by
  intro i j hij
  simp [degradedMatrix, degradationMatrix_apply, hij, hA i j hij]

/-- Physical spectral criticality: zero is a real spectral bound, its mode is
strictly positive and normalized, and the degradation vector is physical. -/
def PhysicalSpectralCritical [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) : Prop :=
  NonnegativeVector d ∧
    ∃ v, NormalizedPositive v ∧
      Matrix.mulVec (degradedMatrix A d) v = 0 ∧
      IsRealSpectralBound (degradedMatrix A d) 0

/-- The formerly missing semantic bridge. For a Metzler source matrix, the
normalized projective formula is equivalent to a physical zero-spectral-bound
critical point, not merely to possession of an arbitrary positive nullvector. -/
theorem physicalSpectralCritical_iff_projective
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) (hA : IsMetzler A) :
    PhysicalSpectralCritical A d ↔
      ∃ v, NormalizedPositive v ∧
        NonnegativeVector (projectiveDegradation A v) ∧
        d = projectiveDegradation A v := by
  constructor
  · rintro ⟨hd, v, hv, hker, _⟩
    have hv0 : ∀ i, v i ≠ 0 := fun i => ne_of_gt (hv.1 i)
    have hrecover := critical_determines_degradation A d v hv0 hker
    refine ⟨v, hv, ?_, hrecover⟩
    intro i
    rw [← hrecover]
    exact hd i
  · rintro ⟨v, hv, hd, rfl⟩
    have hker := projectiveDegradation_is_critical A v
      (fun i => ne_of_gt (hv.1 i))
    refine ⟨hd, v, hv, hker, ?_⟩
    apply positiveEigenvector_isRealSpectralBound
      (degradedMatrix_isMetzler hA _) hv.1
    simpa using hker

/-- Projective degradation at prescribed real spectral bound `lam`. -/
noncomputable def shiftedProjectiveDegradation [Fintype ι]
    (A : Matrix ι ι ℝ) (v : ι → ℝ) (lam : ℝ) (i : ι) : ℝ :=
  projectiveDegradation A v i - lam

/-- A physical onset state at spectral bound `lam`: the bound is an actual
dominant real eigenvalue and has a normalized strictly positive mode. -/
def PhysicalSpectralState [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) (lam : ℝ) : Prop :=
  NonnegativeVector d ∧
    ∃ v, NormalizedPositive v ∧
      Matrix.mulVec (degradedMatrix A d) v = lam • v ∧
      IsRealSpectralBound (degradedMatrix A d) lam

theorem eigenvector_determines_shiftedDegradation
    [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d v : ι → ℝ) (lam : ℝ)
    (hv : StrictlyPositive v)
    (heig : Matrix.mulVec (degradedMatrix A d) v = lam • v) :
    d = shiftedProjectiveDegradation A v lam := by
  funext i
  have hi := congrFun heig i
  simp only [degraded_mulVec_apply, Pi.smul_apply, smul_eq_mul] at hi
  dsimp [shiftedProjectiveDegradation, projectiveDegradation]
  apply (eq_sub_iff_add_eq).2
  apply (eq_div_iff (ne_of_gt (hv i))).2
  linarith

theorem shiftedProjectiveDegradation_is_eigenvector
    [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (v : ι → ℝ) (lam : ℝ)
    (hv : StrictlyPositive v) :
    Matrix.mulVec (degradedMatrix A (shiftedProjectiveDegradation A v lam)) v =
      lam • v := by
  ext i
  rw [degraded_mulVec_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  dsimp [shiftedProjectiveDegradation, projectiveDegradation]
  field_simp [ne_of_gt (hv i)]
  ring

/-- Exact arbitrary-degradation onset parametrization. The sign of `lam`
selects growth, criticality, or extinction, while the theorem itself verifies
that `lam` dominates the real parts of every complex eigenvalue. -/
theorem physicalSpectralState_iff_shiftedProjective
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) (lam : ℝ) (hA : IsMetzler A) :
    PhysicalSpectralState A d lam ↔
      ∃ v, NormalizedPositive v ∧
        NonnegativeVector (shiftedProjectiveDegradation A v lam) ∧
        d = shiftedProjectiveDegradation A v lam := by
  constructor
  · rintro ⟨hd, v, hv, heig, _⟩
    have hrecover := eigenvector_determines_shiftedDegradation A d v lam hv.1 heig
    refine ⟨v, hv, ?_, hrecover⟩
    intro i
    rw [← hrecover]
    exact hd i
  · rintro ⟨v, hv, hd, rfl⟩
    have heig := shiftedProjectiveDegradation_is_eigenvector A v lam hv.1
    refine ⟨hd, v, hv, heig, ?_⟩
    exact positiveEigenvector_isRealSpectralBound
      (degradedMatrix_isMetzler hA _) hv.1 heig

/-- Source-faithful form of the arbitrary-degradation spectral theorem. -/
theorem sourceNetwork_physicalSpectralState_iff
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (rs : List (UnaryReaction ι)) (d : ι → ℝ) (lam : ℝ)
    (hrs : ∀ r ∈ rs, NonnegativeReaction r) :
    PhysicalSpectralState (reactionPart rs) d lam ↔
      ∃ v, NormalizedPositive v ∧
        NonnegativeVector (shiftedProjectiveDegradation (reactionPart rs) v lam) ∧
        d = shiftedProjectiveDegradation (reactionPart rs) v lam := by
  apply physicalSpectralState_iff_shiftedProjective
  intro i j hij
  exact reactionPart_offDiag_nonneg rs hrs hij

def PhysicalSpectralGrowth [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) : Prop :=
  ∃ lam, 0 < lam ∧ PhysicalSpectralState A d lam

def PhysicalSpectralExtinction [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) : Prop :=
  ∃ lam, lam < 0 ∧ PhysicalSpectralState A d lam

theorem sourceNetwork_spectralGrowth_iff
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (rs : List (UnaryReaction ι)) (d : ι → ℝ)
    (hrs : ∀ r ∈ rs, NonnegativeReaction r) :
    PhysicalSpectralGrowth (reactionPart rs) d ↔
      ∃ lam, 0 < lam ∧ ∃ v, NormalizedPositive v ∧
        NonnegativeVector (shiftedProjectiveDegradation (reactionPart rs) v lam) ∧
        d = shiftedProjectiveDegradation (reactionPart rs) v lam := by
  constructor
  · rintro ⟨lam, hlam, hstate⟩
    exact ⟨lam, hlam, (sourceNetwork_physicalSpectralState_iff rs d lam hrs).mp hstate⟩
  · rintro ⟨lam, hlam, hprojective⟩
    exact ⟨lam, hlam, (sourceNetwork_physicalSpectralState_iff rs d lam hrs).mpr hprojective⟩

theorem sourceNetwork_spectralCritical_iff
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (rs : List (UnaryReaction ι)) (d : ι → ℝ)
    (hrs : ∀ r ∈ rs, NonnegativeReaction r) :
    PhysicalSpectralCritical (reactionPart rs) d ↔
      ∃ v, NormalizedPositive v ∧
        NonnegativeVector (projectiveDegradation (reactionPart rs) v) ∧
        d = projectiveDegradation (reactionPart rs) v := by
  apply physicalSpectralCritical_iff_projective
  intro i j hij
  exact reactionPart_offDiag_nonneg rs hrs hij

theorem sourceNetwork_spectralExtinction_iff
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (rs : List (UnaryReaction ι)) (d : ι → ℝ)
    (hrs : ∀ r ∈ rs, NonnegativeReaction r) :
    PhysicalSpectralExtinction (reactionPart rs) d ↔
      ∃ lam, lam < 0 ∧ ∃ v, NormalizedPositive v ∧
        NonnegativeVector (shiftedProjectiveDegradation (reactionPart rs) v lam) ∧
        d = shiftedProjectiveDegradation (reactionPart rs) v lam := by
  constructor
  · rintro ⟨lam, hlam, hstate⟩
    exact ⟨lam, hlam, (sourceNetwork_physicalSpectralState_iff rs d lam hrs).mp hstate⟩
  · rintro ⟨lam, hlam, hprojective⟩
    exact ⟨lam, hlam, (sourceNetwork_physicalSpectralState_iff rs d lam hrs).mpr hprojective⟩

end DegradationControl
