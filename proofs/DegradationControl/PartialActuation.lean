import proofs.DegradationControl.PerronExistence

namespace DegradationControl

section GeneralPartialActuation

variable {U S : Type*} [Fintype U] [Fintype S]
  [DecidableEq U] [DecidableEq S]

/-- The principal subsystem on the unactuated coordinates. -/
def unactuatedBlock (A : Matrix (U ⊕ S) (U ⊕ S) ℝ) : Matrix U U ℝ :=
  A.submatrix Sum.inl Sum.inl

/-- A degradation vector is physically admissible and supported only on the
actuated coordinates. -/
def SupportedActuatedDegradation (d : (U ⊕ S) → ℝ) : Prop :=
  NonnegativeVector d ∧ ∀ i : U, d (Sum.inl i) = 0

/-- Stabilizability expressed by the strict positive-vector certificate. -/
def PartiallyStabilizable (A : Matrix (U ⊕ S) (U ⊕ S) ℝ) : Prop :=
  ∃ d, SupportedActuatedDegradation d ∧
    ExtinctionCertificate (degradedMatrix A d)

/-- Exact arbitrary-finite actuator-placement theorem.  A Metzler system can
be made strictly extinct by finite nonnegative degradation on precisely the
`S` coordinates iff the unactuated principal block already has a strict
extinction (Hurwitz) certificate. -/
theorem partialActuation_stabilizable_iff_unactuatedCertificate
    (A : Matrix (U ⊕ S) (U ⊕ S) ℝ) (hA : IsMetzler A) :
    PartiallyStabilizable A ↔ ExtinctionCertificate (unactuatedBlock A) := by
  constructor
  · rintro ⟨d, ⟨hdnonneg, hdU⟩, hcert⟩
    obtain ⟨v, hv, hproj⟩ :=
      (extinctionCertificate_degraded_iff_projective_gt A d).mp hcert
    let u : U → ℝ := fun i ↦ v (Sum.inl i)
    refine ⟨u, fun i ↦ hv (Sum.inl i), ?_⟩
    intro i
    let cross : ℝ := ∑ s : S, A (Sum.inl i) (Sum.inr s) * v (Sum.inr s)
    have hcross : 0 ≤ cross := by
      dsimp [cross]
      apply Finset.sum_nonneg
      intro s _
      exact mul_nonneg (hA _ _ Sum.inl_ne_inr) (le_of_lt (hv _))
    have hAvneg : A.mulVec v (Sum.inl i) < 0 := by
      have hi := hproj (Sum.inl i)
      rw [hdU i] at hi
      have hmul := (div_lt_iff₀ (hv (Sum.inl i))).mp hi
      simpa using hmul
    have hsplit :
        A.mulVec v (Sum.inl i) =
          (unactuatedBlock A).mulVec u i + cross := by
      change (fun j ↦ A (Sum.inl i) j) ⬝ᵥ v =
        (fun j ↦ A (Sum.inl i) (Sum.inl j)) ⬝ᵥ u + cross
      rw [Matrix.dotProduct_block]
      rfl
    linarith
  · rintro ⟨u, hu, hUneg⟩
    let margin : U → ℝ := fun i ↦ -((unactuatedBlock A).mulVec u i)
    let cross : U → ℝ := fun i ↦
      ∑ s : S, A (Sum.inl i) (Sum.inr s)
    have hmargin (i : U) : 0 < margin i := by
      dsimp [margin]
      exact neg_pos.mpr (hUneg i)
    have hcross (i : U) : 0 ≤ cross i := by
      dsimp [cross]
      apply Finset.sum_nonneg
      intro s _
      exact hA _ _ Sum.inl_ne_inr
    let term : U → ℝ := fun i ↦ (cross i + 1) / margin i
    let T : ℝ := ∑ i, term i
    have hterm (i : U) : 0 ≤ term i := by
      dsimp [term]
      exact div_nonneg (by linarith [hcross i]) (le_of_lt (hmargin i))
    have hT : 0 ≤ T := by
      dsimp [T]
      exact Finset.sum_nonneg (fun i _ ↦ hterm i)
    let eps : ℝ := 1 / (1 + T)
    have heps : 0 < eps := by
      dsimp [eps]
      positivity
    have heps_cross (i : U) : eps * cross i < margin i := by
      have hratio : term i ≤ T := by
        dsimp [T]
        exact Finset.single_le_sum (fun j _ ↦ hterm j) (Finset.mem_univ i)
      have hcle : cross i + 1 ≤ T * margin i := by
        exact (div_le_iff₀ (hmargin i)).mp hratio
      have hden : 0 < 1 + T := by linarith
      have hfrac : (cross i + 1) / (1 + T) < margin i := by
        apply (div_lt_iff₀ hden).2
        nlinarith [hmargin i]
      have hmul : eps * cross i < eps * (cross i + 1) := by
        exact mul_lt_mul_of_pos_left (by linarith) heps
      have heq : eps * (cross i + 1) = (cross i + 1) / (1 + T) := by
        simp [eps, div_eq_mul_inv, mul_comm]
      rw [heq] at hmul
      exact lt_trans hmul hfrac
    let v : (U ⊕ S) → ℝ := Sum.elim u (fun _ ↦ eps)
    have hv : StrictlyPositive v := by
      intro x
      cases x with
      | inl i => exact hu i
      | inr s => exact heps
    have hAvU (i : U) : A.mulVec v (Sum.inl i) < 0 := by
      have hsplit :
          A.mulVec v (Sum.inl i) =
            (unactuatedBlock A).mulVec u i + eps * cross i := by
        change (fun j ↦ A (Sum.inl i) j) ⬝ᵥ v =
          (fun j ↦ A (Sum.inl i) (Sum.inl j)) ⬝ᵥ u +
            eps * ∑ s : S, A (Sum.inl i) (Sum.inr s)
        rw [Matrix.dotProduct_block]
        simp [v, Function.comp_apply, dotProduct, Finset.mul_sum, mul_comm]
      rw [hsplit]
      have hm := heps_cross i
      dsimp [margin] at hm
      linarith
    let d : (U ⊕ S) → ℝ
      | Sum.inl _ => 0
      | Sum.inr s => max 0 (projectiveDegradation A v (Sum.inr s) + 1)
    have hdnonneg : NonnegativeVector d := by
      intro x
      cases x with
      | inl i => simp [d]
      | inr s => exact le_max_left _ _
    have hdU : ∀ i : U, d (Sum.inl i) = 0 := by
      intro i
      rfl
    refine ⟨d, ⟨hdnonneg, hdU⟩,
      (extinctionCertificate_degraded_iff_projective_gt A d).mpr
        ⟨v, hv, ?_⟩⟩
    intro x
    cases x with
    | inl i =>
        simp only [d]
        apply (div_lt_iff₀ (hv (Sum.inl i))).2
        simpa using hAvU i
    | inr s =>
        dsimp [d]
        by_cases h : 0 ≤ projectiveDegradation A v (Sum.inr s) + 1
        · rw [max_eq_right h]
          linarith
        · rw [max_eq_left (le_of_not_ge h)]
          linarith

/-- Genuine spectral supported stabilizability. -/
def SpectrallyPartiallyStabilizable
    (A : Matrix (U ⊕ S) (U ⊕ S) ℝ) : Prop :=
  ∃ d, SupportedActuatedDegradation d ∧
    HasNegativeRealSpectralBound (degradedMatrix A d)

/-- Spectral form of the arbitrary-finite actuator-placement theorem.  Under
the explicit irreducible-Metzler hypotheses for the full system and the
unactuated principal block, finite supported diagonal stabilization is
equivalent to negative real spectral bound of that block. -/
theorem partialActuation_spectralStabilizable_iff_unactuatedHurwitz
    [Nonempty U] [Nonempty S]
    (A : Matrix (U ⊕ S) (U ⊕ S) ℝ) (hA : IsMetzler A)
    (hirrA : HasIrreducibleNonnegativeShift A)
    (hirrU : HasIrreducibleNonnegativeShift (unactuatedBlock A)) :
    SpectrallyPartiallyStabilizable A ↔
      HasNegativeRealSpectralBound (unactuatedBlock A) := by
  have hU : IsMetzler (unactuatedBlock A) := by
    intro i j hij
    apply hA (Sum.inl i) (Sum.inl j)
    exact fun h ↦ hij (Sum.inl_injective h)
  constructor
  · rintro ⟨d, hd, hspectral⟩
    have hMd : IsMetzler (degradedMatrix A d) := degradedMatrix_isMetzler hA d
    have hirrd := hasIrreducibleNonnegativeShift_degradedMatrix A d hirrA
    have hcert : ExtinctionCertificate (degradedMatrix A d) :=
      (irreducibleMetzler_negativeSpectralBound_iff_extinctionCertificate
        _ hMd hirrd).mp hspectral
    have hUcert : ExtinctionCertificate (unactuatedBlock A) :=
      (partialActuation_stabilizable_iff_unactuatedCertificate A hA).mp
        ⟨d, hd, hcert⟩
    exact (irreducibleMetzler_negativeSpectralBound_iff_extinctionCertificate
      _ hU hirrU).mpr hUcert
  · intro hUspectral
    have hUcert : ExtinctionCertificate (unactuatedBlock A) :=
      (irreducibleMetzler_negativeSpectralBound_iff_extinctionCertificate
        _ hU hirrU).mp hUspectral
    obtain ⟨d, hd, hcert⟩ :=
      (partialActuation_stabilizable_iff_unactuatedCertificate A hA).mpr hUcert
    have hMd : IsMetzler (degradedMatrix A d) := degradedMatrix_isMetzler hA d
    have hirrd := hasIrreducibleNonnegativeShift_degradedMatrix A d hirrA
    exact ⟨d, hd,
      (irreducibleMetzler_negativeSpectralBound_iff_extinctionCertificate
        _ hMd hirrd).mpr hcert⟩

end GeneralPartialActuation

def stableUncontrolledFamily (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![-(1 + a), 2], ![2, -1]]

def marginalUncontrolledFamily (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![-(1 + a), 1], ![1, 0]]

noncomputable def growingUncontrolledFamily (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![-(1 + a), 1], ![1, (1 : ℝ) / 2]]

theorem stableUncontrolledFamily_det (a : ℝ) :
    Matrix.det (stableUncontrolledFamily a) = a - 3 := by
  rw [Matrix.det_fin_two]
  simp [stableUncontrolledFamily]
  ring

theorem marginalUncontrolledFamily_det (a : ℝ) :
    Matrix.det (marginalUncontrolledFamily a) = -1 := by
  rw [Matrix.det_fin_two]
  simp [marginalUncontrolledFamily]

theorem growingUncontrolledFamily_det (a : ℝ) :
    Matrix.det (growingUncontrolledFamily a) = -(a + 3) / 2 := by
  rw [Matrix.det_fin_two]
  simp [growingUncontrolledFamily]
  ring

end DegradationControl
