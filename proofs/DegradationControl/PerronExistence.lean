import proofs.DegradationControl.SpectralSemantics
import proofs.DegradationControl.PositivePerron
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

namespace DegradationControl

open Set

def IsPositiveMatrix (P : Matrix ι ι ℝ) : Prop := ∀ i j, 0 < P i j

noncomputable def totalOutput [Fintype ι] (P : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, P.mulVec x i

noncomputable def normalizedMulVec [Fintype ι]
    (P : Matrix ι ι ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i ↦ P.mulVec x i / totalOutput P x

theorem mulVec_pos_of_positive_of_mem_stdSimplex
    [Fintype ι] [Nonempty ι]
    {P : Matrix ι ι ℝ} (hP : IsPositiveMatrix P)
    {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι) (i : ι) :
    0 < P.mulVec x i := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < x j := by
    by_contra h
    push Not at h
    have hx0 : x = 0 := by
      funext k
      exact le_antisymm (h k) (hx.1 k)
    simpa [hx0] using hx.2
  exact Finset.sum_pos' (fun k _ ↦ mul_nonneg (le_of_lt (hP i k)) (hx.1 k))
    ⟨j, Finset.mem_univ j, mul_pos (hP i j) hj⟩

theorem totalOutput_pos_of_positive_of_mem_stdSimplex
    [Fintype ι] [Nonempty ι]
    {P : Matrix ι ι ℝ} (hP : IsPositiveMatrix P)
    {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι) :
    0 < totalOutput P x := by
  apply Finset.sum_pos
  · intro i _
    exact mulVec_pos_of_positive_of_mem_stdSimplex hP hx i
  · exact Finset.univ_nonempty

theorem normalizedMulVec_mem_stdSimplex
    [Fintype ι] [Nonempty ι]
    {P : Matrix ι ι ℝ} (hP : IsPositiveMatrix P)
    {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι) :
    normalizedMulVec P x ∈ stdSimplex ℝ ι := by
  have htot := totalOutput_pos_of_positive_of_mem_stdSimplex hP hx
  constructor
  · intro i
    exact div_nonneg (le_of_lt (mulVec_pos_of_positive_of_mem_stdSimplex hP hx i))
      (le_of_lt htot)
  · simp only [normalizedMulVec, ← Finset.sum_div, totalOutput]
    exact div_self (ne_of_gt htot)

theorem continuous_normalizedMulVecOn
    [Fintype ι] [Nonempty ι]
    {P : Matrix ι ι ℝ} (hP : IsPositiveMatrix P) :
    ContinuousOn (normalizedMulVec P) (stdSimplex ℝ ι) := by
  rw [continuousOn_pi]
  intro i
  apply ContinuousOn.div
  · fun_prop
  · apply Continuous.continuousOn
    unfold totalOutput
    fun_prop
  · intro x hx
    exact ne_of_gt (totalOutput_pos_of_positive_of_mem_stdSimplex hP hx)

/-- Perron existence for an entrywise-positive finite real matrix, via the
independent Collatz–Wielandt proof in `PositivePerron`. -/
theorem positiveMatrix_exists_normalizedPositive_eigenvector
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {P : Matrix ι ι ℝ} (hP : IsPositiveMatrix P) :
    ∃ rho : ℝ, 0 < rho ∧ ∃ v : ι → ℝ,
      NormalizedPositive v ∧ P.mulVec v = rho • v := by
  obtain ⟨rho, hrho, v, hvpos, hvsum, hv⟩ := PositivePerron.exists_perron hP
  exact ⟨rho, hrho, v, ⟨hvpos, hvsum⟩, hv⟩

theorem positiveMatrix_exists_normalizedPositive_fixedEigenvector
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {P : Matrix ι ι ℝ} (hP : IsPositiveMatrix P) :
    ∃ v : ι → ℝ, NormalizedPositive v ∧
      P.mulVec v = totalOutput P v • v := by
  obtain ⟨rho, _, v, hv, heig⟩ :=
    positiveMatrix_exists_normalizedPositive_eigenvector hP
  have hsum := congrArg (∑ i, · i) heig
  have hrho : totalOutput P v = rho := by
    calc
      totalOutput P v = ∑ i, rho * v i := by
        simpa only [totalOutput, Pi.smul_apply, smul_eq_mul] using hsum
      _ = rho * ∑ i, v i := by rw [Finset.mul_sum]
      _ = rho := by rw [hv.2, mul_one]
  exact ⟨v, hv, by simpa [hrho] using heig⟩

noncomputable def positiveRegularization [Fintype ι]
    (A : Matrix ι ι ℝ) (n : ℕ) : Matrix ι ι ℝ :=
  fun i j ↦ A i j + ((n + 1 : ℕ) : ℝ)⁻¹

theorem positiveRegularization_isPositive [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j) (n : ℕ) :
    IsPositiveMatrix (positiveRegularization A n) := by
  intro i j
  exact add_pos_of_nonneg_of_pos (hA i j) (inv_pos.mpr (by positivity))

noncomputable def regularizedPerronVector
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (n : ℕ) : ι → ℝ :=
  Classical.choose (positiveMatrix_exists_normalizedPositive_fixedEigenvector
    (positiveRegularization_isPositive hA n))

theorem regularizedPerronVector_spec
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (n : ℕ) :
    NormalizedPositive (regularizedPerronVector A hA n) ∧
      (positiveRegularization A n).mulVec (regularizedPerronVector A hA n) =
        totalOutput (positiveRegularization A n) (regularizedPerronVector A hA n) •
          regularizedPerronVector A hA n :=
  Classical.choose_spec (positiveMatrix_exists_normalizedPositive_fixedEigenvector
    (positiveRegularization_isPositive hA n))

/-- Compactness limit of positive regularizations.  No irreducibility is needed
for existence of a normalized nonnegative real eigenvector. -/
theorem nonnegativeMatrix_exists_normalizedNonnegative_eigenvector
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    ∃ rho : ℝ, ∃ v : ι → ℝ, v ∈ stdSimplex ℝ ι ∧ A.mulVec v = rho • v := by
  let u : ℕ → (ι → ℝ) := fun n ↦ regularizedPerronVector A hA n
  have huS : ∀ n, u n ∈ stdSimplex ℝ ι := by
    intro n
    exact ⟨fun i ↦ le_of_lt ((regularizedPerronVector_spec A hA n).1.1 i),
      (regularizedPerronVector_spec A hA n).1.2⟩
  obtain ⟨v, hvS, φ, hφ, hvlim⟩ := (isCompact_stdSimplex ℝ ι).tendsto_subseq huS
  have hεbase : Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_nhds_zero_nat
  have hε : Filter.Tendsto (fun n ↦ ((((φ n) + 1 : ℕ) : ℝ))⁻¹)
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (hεbase.comp (Filter.tendsto_add_atTop_nat 1)).comp hφ.tendsto_atTop
  let rho := totalOutput A v
  refine ⟨rho, v, hvS, ?_⟩
  funext i
  have hpair : Filter.Tendsto
      (fun n ↦ (((((φ n) + 1 : ℕ) : ℝ))⁻¹, u (φ n)))
      Filter.atTop (nhds (0, v)) := by
    simpa [Function.comp_def, nhds_prod_eq] using hε.prodMk hvlim
  have hleft : Filter.Tendsto
      (fun n ↦ ∑ j, (A i j + ((((φ n) + 1 : ℕ) : ℝ))⁻¹) * u (φ n) j)
      Filter.atTop (nhds (A.mulVec v i)) := by
    have hc : Continuous (fun p : ℝ × (ι → ℝ) ↦ ∑ j, (A i j + p.1) * p.2 j) := by
      fun_prop
    simpa [Function.comp_def, Matrix.mulVec, dotProduct] using hc.continuousAt.tendsto.comp hpair
  have hright : Filter.Tendsto
      (fun n ↦
        (∑ k, ∑ j, (A k j + ((((φ n) + 1 : ℕ) : ℝ))⁻¹) * u (φ n) j) *
          u (φ n) i)
      Filter.atTop (nhds (rho * v i)) := by
    have hc : Continuous (fun p : ℝ × (ι → ℝ) ↦
        (∑ k, ∑ j, (A k j + p.1) * p.2 j) * p.2 i) := by
      fun_prop
    simpa [Function.comp_def, rho, totalOutput, Matrix.mulVec, dotProduct] using
      hc.continuousAt.tendsto.comp hpair
  have heq : ∀ n,
      (∑ j, (A i j + ((((φ n) + 1 : ℕ) : ℝ))⁻¹) * u (φ n) j) =
        (∑ k, ∑ j, (A k j + ((((φ n) + 1 : ℕ) : ℝ))⁻¹) * u (φ n) j) *
          u (φ n) i := by
    intro n
    have hi := congrFun (regularizedPerronVector_spec A hA (φ n)).2 i
    simpa [u, positiveRegularization, totalOutput, Matrix.mulVec, dotProduct,
      Pi.smul_apply, smul_eq_mul] using hi
  have hright' := hright.congr' (Filter.Eventually.of_forall fun n ↦ (heq n).symm)
  exact tendsto_nhds_unique hleft hright'

theorem pow_mulVec_eigenvector
    [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (v : ι → ℝ) (rho : ℝ)
    (heig : A.mulVec v = rho • v) (k : ℕ) :
    (A ^ k).mulVec v = rho ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul, ih,
        smul_smul, pow_succ]
      rw [mul_comm]

theorem irreducibleNonnegative_eigenvector_strictlyPositive
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hirr : A.IsIrreducible) {v : ι → ℝ} {rho : ℝ}
    (hvS : v ∈ stdSimplex ℝ ι) (heig : A.mulVec v = rho • v) :
    StrictlyPositive v := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < v j := by
    by_contra h
    push Not at h
    have hv0 : v = 0 := by
      funext q
      exact le_antisymm (h q) (hvS.1 q)
    simpa [hv0] using hvS.2
  intro i
  by_contra hi
  have hvi : v i = 0 := le_antisymm (le_of_not_gt hi) (hvS.1 i)
  obtain ⟨k, _, hk⟩ := (Matrix.isIrreducible_iff_exists_pow_pos hA).mp hirr i j
  have hpowNonneg : ∀ p q, 0 ≤ (A ^ k) p q := Matrix.pow_apply_nonneg hA k
  have hpositive : 0 < (A ^ k).mulVec v i := by
    apply Finset.sum_pos'
    · intro q _
      exact mul_nonneg (hpowNonneg i q) (hvS.1 q)
    · exact ⟨j, Finset.mem_univ j, mul_pos hk hj⟩
  have hpowEq := congrFun (pow_mulVec_eigenvector A v rho heig k) i
  simp only [Pi.smul_apply, smul_eq_mul, hvi, mul_zero] at hpowEq
  exact (ne_of_gt hpositive) hpowEq

/-- Perron existence and spectral dominance for an irreducible nonnegative
matrix, obtained by positive regularization and compactness. -/
theorem irreducibleNonnegative_exists_realSpectralBound
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hirr : A.IsIrreducible) :
    ∃ rho : ℝ, ∃ v : ι → ℝ, NormalizedPositive v ∧
      A.mulVec v = rho • v ∧ IsRealSpectralBound A rho := by
  obtain ⟨rho, v, hvS, heig⟩ :=
    nonnegativeMatrix_exists_normalizedNonnegative_eigenvector A hA
  have hvpos := irreducibleNonnegative_eigenvector_strictlyPositive hA hirr hvS heig
  refine ⟨rho, v, ⟨hvpos, hvS.2⟩, heig, ?_⟩
  exact positiveEigenvector_isRealSpectralBound
    (fun i j _ ↦ hA i j) hvpos heig

noncomputable def scalarShift [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (c : ℝ) : Matrix ι ι ℝ :=
  M + c • (1 : Matrix ι ι ℝ)

theorem scalarShift_mulVec [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (c : ℝ) (v : ι → ℝ) :
    (scalarShift M c).mulVec v = M.mulVec v + c • v := by
  unfold scalarShift
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- Shift-stable irreducibility for a Metzler matrix: some scalar diagonal
shift is an irreducible nonnegative matrix.  This is the standard
finite-dimensional irreducible-Metzler hypothesis in a form directly usable
by Mathlib's nonnegative-matrix graph API. -/
def HasIrreducibleNonnegativeShift [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : Prop :=
  ∃ c : ℝ, (∀ i j, 0 ≤ scalarShift M c i j) ∧
    (scalarShift M c).IsIrreducible

/-- Entrywise enlargement of a nonnegative irreducible matrix remains
irreducible.  The proof maps each positive-edge path into the larger matrix. -/
theorem irreducible_of_entrywise_le
    [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.IsIrreducible)
    (hAB : ∀ i j, A i j ≤ B i j) (hB : ∀ i j, 0 ≤ B i j) :
    B.IsIrreducible := by
  have hpow_le : ∀ k i j, (A ^ k) i j ≤ (B ^ k) i j := by
    intro k
    induction k with
    | zero => intro i j; rfl
    | succ k ih =>
        intro i j
        rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul (ih i x) (hAB x j) (hA.nonneg x j)
          (Matrix.pow_apply_nonneg hB k i x)
  rw [Matrix.isIrreducible_iff_exists_pow_pos hB]
  intro i j
  obtain ⟨k, hk, hpos⟩ :=
    (Matrix.isIrreducible_iff_exists_pow_pos hA.nonneg).mp hA i j
  exact ⟨k, hk, lt_of_lt_of_le hpos (hpow_le k i j)⟩

/-- Arbitrary diagonal degradation preserves irreducible-Metzler structure in
the shift formulation.  A larger scalar shift compensates every diagonal
change, while all off-diagonal positive edges are unchanged. -/
theorem hasIrreducibleNonnegativeShift_degradedMatrix
    [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (d : ι → ℝ)
    (hirr : HasIrreducibleNonnegativeShift M) :
    HasIrreducibleNonnegativeShift (degradedMatrix M d) := by
  obtain ⟨c, hNnonneg, hNirr⟩ := hirr
  let D : ℝ := ∑ i, |d i|
  let c' : ℝ := c + D
  have hd_le (i : ι) : d i ≤ D := by
    have habs : |d i| ≤ D := by
      dsimp [D]
      exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (d j)) (Finset.mem_univ i)
    exact le_trans (le_abs_self (d i)) habs
  have hle : ∀ i j, scalarShift M c i j ≤
      scalarShift (degradedMatrix M d) c' i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      have hleft : scalarShift M c i i = M i i + c := by simp [scalarShift]
      have hright : scalarShift (degradedMatrix M d) c' i i =
          M i i - d i + c' := by
        simp [scalarShift, degradedMatrix, degradationMatrix]
        ring
      rw [hleft, hright]
      dsimp [c']
      linarith [hd_le i]
    · simp [scalarShift, degradedMatrix, degradationMatrix, hij]
  have hBnonneg : ∀ i j, 0 ≤ scalarShift (degradedMatrix M d) c' i j := by
    intro i j
    exact le_trans (hNnonneg i j) (hle i j)
  exact ⟨c', hBnonneg, irreducible_of_entrywise_le hNirr hle hBnonneg⟩

/-- Source strong connectivity survives every diagonal degradation: a finite
scalar shift makes the degraded source matrix nonnegative with a positive
diagonal, while its positive off-diagonal graph is unchanged. -/
theorem sourceIrreducible_hasIrreducibleNonnegativeShift
    [Fintype ι] [DecidableEq ι]
    (rs : List (UnaryReaction ι)) (d : ι → ℝ)
    (hrs : ∀ r ∈ rs, NonnegativeReaction r)
    (hsource : SourceIrreducible rs) :
    HasIrreducibleNonnegativeShift
      (degradedMatrix (reactionPart rs) d) := by
  let M := degradedMatrix (reactionPart rs) d
  let S : ℝ := ∑ i, |M i i|
  let c : ℝ := 1 + S
  have habs_le_sum (i : ι) : |M i i| ≤ S := by
    dsimp [S]
    exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (M j j)) (Finset.mem_univ i)
  have hdiag (i : ι) : 1 ≤ scalarShift M c i i := by
    have hlower : -S ≤ M i i :=
      le_trans (neg_le_neg (habs_le_sum i)) (neg_abs_le (M i i))
    have heq : scalarShift M c i i = M i i + c := by
      simp [scalarShift]
    rw [heq]
    dsimp [c]
    linarith
  have hnonneg : ∀ i j, 0 ≤ scalarShift M c i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact le_trans zero_le_one (hdiag i)
    · have heq : scalarShift M c i j = reactionPart rs i j := by
        simp [M, scalarShift, degradedMatrix, degradationMatrix, hij]
      rw [heq]
      exact reactionPart_offDiag_nonneg rs hrs hij
  refine ⟨c, hnonneg, ?_⟩
  apply irreducible_of_entrywise_le hsource
  · intro i j
    by_cases hij : i = j
    · subst j
      change sourceAdjacency rs i i ≤ scalarShift M c i i
      rw [show sourceAdjacency rs i i = 1 by simp [sourceAdjacency]]
      exact hdiag i
    · rw [sourceAdjacency_offDiag_eq rs hrs hij]
      have heq : scalarShift M c i j = reactionPart rs i j := by
        simp [M, scalarShift, degradedMatrix, degradationMatrix, hij]
      rw [heq]
  · exact hnonneg

/-- Perron--Frobenius existence for an irreducible Metzler matrix.  Unlike the
earlier Gershgorin bridge, this theorem does not assume a positive eigenmode:
it constructs one and proves that its eigenvalue is the real spectral bound. -/
theorem irreducibleMetzler_exists_realSpectralBound
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : IsMetzler M)
    (hirr : HasIrreducibleNonnegativeShift M) :
    ∃ lam : ℝ, ∃ v : ι → ℝ, NormalizedPositive v ∧
      M.mulVec v = lam • v ∧ IsRealSpectralBound M lam := by
  obtain ⟨c, hnonneg, hshiftIrr⟩ := hirr
  obtain ⟨rho, v, hv, hshiftEig, _⟩ :=
    irreducibleNonnegative_exists_realSpectralBound (scalarShift M c) hnonneg hshiftIrr
  let lam := rho - c
  have heig : M.mulVec v = lam • v := by
    have h := hshiftEig
    rw [scalarShift_mulVec] at h
    ext i
    have hi := congrFun h i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    dsimp [lam]
    linarith
  refine ⟨lam, v, hv, heig, ?_⟩
  exact positiveEigenvector_isRealSpectralBound hM hv.1 heig

/-- Exact Perron semantic equivalence: under irreducible Metzler hypotheses,
being the real spectral bound is equivalent to possessing a normalized
strictly positive eigenvector. -/
theorem irreducibleMetzler_isRealSpectralBound_iff_positiveEigenvector
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : IsMetzler M)
    (hirr : HasIrreducibleNonnegativeShift M) (lam : ℝ) :
    IsRealSpectralBound M lam ↔
      ∃ v : ι → ℝ, NormalizedPositive v ∧ M.mulVec v = lam • v := by
  constructor
  · intro hlam
    obtain ⟨rho, v, hv, heig, hrho⟩ :=
      irreducibleMetzler_exists_realSpectralBound M hM hirr
    have hle : lam ≤ rho := hrho.2 (lam : ℂ) hlam.1
    have hge : rho ≤ lam := hlam.2 (rho : ℂ) hrho.1
    have hlr : lam = rho := le_antisymm hle hge
    exact ⟨v, hv, by simpa [hlr] using heig⟩
  · rintro ⟨v, hv, heig⟩
    exact positiveEigenvector_isRealSpectralBound hM hv.1 heig

/-- The non-circular physical spectral state: degradation is nonnegative and
`lam` is the actual real spectral bound.  No eigenvector is included in the
definition. -/
def IrreduciblePhysicalSpectralState [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) (lam : ℝ) : Prop :=
  NonnegativeVector d ∧ IsRealSpectralBound (degradedMatrix A d) lam

/-- Exact arbitrary-degradation parametrization from bare spectral semantics.
Irreducible Perron existence recovers the positive mode; the degradation is
then forced coordinatewise by the projective formula. -/
theorem irreduciblePhysicalSpectralState_iff_shiftedProjective
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) (lam : ℝ)
    (hA : IsMetzler A)
    (hirr : HasIrreducibleNonnegativeShift (degradedMatrix A d)) :
    IrreduciblePhysicalSpectralState A d lam ↔
      ∃ v, NormalizedPositive v ∧
        NonnegativeVector (shiftedProjectiveDegradation A v lam) ∧
        d = shiftedProjectiveDegradation A v lam := by
  have hMd : IsMetzler (degradedMatrix A d) := degradedMatrix_isMetzler hA d
  constructor
  · rintro ⟨hd, hspectral⟩
    obtain ⟨v, hv, heig⟩ :=
      (irreducibleMetzler_isRealSpectralBound_iff_positiveEigenvector
        (degradedMatrix A d) hMd hirr lam).mp hspectral
    have hrecover := eigenvector_determines_shiftedDegradation A d v lam hv.1 heig
    refine ⟨v, hv, ?_, hrecover⟩
    intro i
    rw [← hrecover]
    exact hd i
  · rintro ⟨v, hv, hd, rfl⟩
    have heig := shiftedProjectiveDegradation_is_eigenvector A v lam hv.1
    refine ⟨hd, positiveEigenvector_isRealSpectralBound ?_ hv.1 heig⟩
    exact degradedMatrix_isMetzler hA _

theorem sourceNetwork_irreducibleSpectralState_iff
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (rs : List (UnaryReaction ι)) (d : ι → ℝ) (lam : ℝ)
    (hrs : ∀ r ∈ rs, NonnegativeReaction r)
    (hirr : HasIrreducibleNonnegativeShift
      (degradedMatrix (reactionPart rs) d)) :
    IrreduciblePhysicalSpectralState (reactionPart rs) d lam ↔
      ∃ v, NormalizedPositive v ∧
        NonnegativeVector
          (shiftedProjectiveDegradation (reactionPart rs) v lam) ∧
        d = shiftedProjectiveDegradation (reactionPart rs) v lam := by
  apply irreduciblePhysicalSpectralState_iff_shiftedProjective
  · intro i j hij
    exact reactionPart_offDiag_nonneg rs hrs hij
  · exact hirr

/-- Zero-spectral-bound boundary in bare spectral language. -/
theorem sourceNetwork_irreducibleCriticalBoundary_iff
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (rs : List (UnaryReaction ι)) (d : ι → ℝ)
    (hrs : ∀ r ∈ rs, NonnegativeReaction r)
    (hirr : HasIrreducibleNonnegativeShift
      (degradedMatrix (reactionPart rs) d)) :
    IrreduciblePhysicalSpectralState (reactionPart rs) d 0 ↔
      ∃ v, NormalizedPositive v ∧
        NonnegativeVector (projectiveDegradation (reactionPart rs) v) ∧
        d = projectiveDegradation (reactionPart rs) v := by
  constructor
  · intro h
    obtain ⟨v, hv, hd, heq⟩ :=
      (sourceNetwork_irreducibleSpectralState_iff rs d 0 hrs hirr).mp h
    refine ⟨v, hv, ?_, ?_⟩
    · intro i
      simpa [shiftedProjectiveDegradation] using hd i
    · funext i
      have hi := congrFun heq i
      simpa [shiftedProjectiveDegradation] using hi
  · rintro ⟨v, hv, hd, heq⟩
    apply (sourceNetwork_irreducibleSpectralState_iff rs d 0 hrs hirr).mpr
    refine ⟨v, hv, ?_, ?_⟩
    · intro i
      simpa [shiftedProjectiveDegradation] using hd i
    · funext i
      have hi := congrFun heq i
      simpa [shiftedProjectiveDegradation] using hi

theorem dotProduct_pos_of_strictlyPositive [Fintype ι] [Nonempty ι]
    {x y : ι → ℝ} (hx : StrictlyPositive x) (hy : StrictlyPositive y) :
    0 < dotProduct x y := by
  apply Finset.sum_pos
  · intro i _
    exact mul_pos (hx i) (hy i)
  · exact Finset.univ_nonempty

theorem dotProduct_neg_of_positive_negative [Fintype ι] [Nonempty ι]
    {x y : ι → ℝ} (hx : StrictlyPositive x) (hy : StrictlyNegative y) :
    dotProduct x y < 0 := by
  have hpos : 0 < dotProduct x (-y) :=
    dotProduct_pos_of_strictlyPositive hx (fun i ↦ neg_pos.mpr (hy i))
  simpa [dotProduct] using hpos

theorem hasIrreducibleNonnegativeShift_transpose
    [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : HasIrreducibleNonnegativeShift M) :
    HasIrreducibleNonnegativeShift M.transpose := by
  obtain ⟨c, hnonneg, hirr⟩ := hM
  refine ⟨c, ?_, ?_⟩
  · intro i j
    simpa [scalarShift, Matrix.transpose_apply, Matrix.one_apply, eq_comm] using hnonneg j i
  · simpa [scalarShift] using hirr.transpose

theorem irreducibleMetzler_positiveLeftEigenvector_at_spectralBound
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : IsMetzler M)
    (hirr : HasIrreducibleNonnegativeShift M) {lam : ℝ}
    (hlam : IsRealSpectralBound M lam) :
    ∃ w : ι → ℝ, NormalizedPositive w ∧ M.transpose.mulVec w = lam • w := by
  have hMT : IsMetzler M.transpose := by
    intro i j hij
    exact hM j i hij.symm
  obtain ⟨rho, w, hw, hwe, _⟩ := irreducibleMetzler_exists_realSpectralBound
    M.transpose hMT (hasIrreducibleNonnegativeShift_transpose hirr)
  obtain ⟨v, hv, hve⟩ :=
    (irreducibleMetzler_isRealSpectralBound_iff_positiveEigenvector
      M hM hirr lam).mp hlam
  have hdot : 0 < dotProduct v w := dotProduct_pos_of_strictlyPositive hv.1 hw.1
  have hbil := Matrix.dotProduct_transpose_mulVec M v w
  rw [hwe, hve] at hbil
  have hbil' : rho * dotProduct v w = lam * dotProduct v w := by
    simpa [dotProduct_smul, dotProduct_comm, smul_eq_mul] using hbil
  have hrho : rho = lam := by nlinarith
  exact ⟨w, hw, by simpa [hrho] using hwe⟩

def HasPositiveRealSpectralBound [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : Prop :=
  ∃ lam, 0 < lam ∧ IsRealSpectralBound M lam

def HasNegativeRealSpectralBound [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : Prop :=
  ∃ lam, lam < 0 ∧ IsRealSpectralBound M lam

theorem irreducibleMetzler_positiveSpectralBound_iff_growthCertificate
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : IsMetzler M)
    (hirr : HasIrreducibleNonnegativeShift M) :
    HasPositiveRealSpectralBound M ↔ GrowthCertificate M := by
  constructor
  · rintro ⟨lam, hlam, hs⟩
    obtain ⟨v, hv, heig⟩ :=
      (irreducibleMetzler_isRealSpectralBound_iff_positiveEigenvector
        M hM hirr lam).mp hs
    refine ⟨v, hv.1, ?_⟩
    intro i
    rw [heig]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_pos hlam (hv.1 i)
  · rintro ⟨z, hz, hMz⟩
    obtain ⟨lam, v, hv, heig, hs⟩ :=
      irreducibleMetzler_exists_realSpectralBound M hM hirr
    obtain ⟨w, hw, hwe⟩ :=
      irreducibleMetzler_positiveLeftEigenvector_at_spectralBound M hM hirr hs
    have hleft : 0 < dotProduct w (M.mulVec z) :=
      dotProduct_pos_of_strictlyPositive hw.1 hMz
    have hbil := Matrix.dotProduct_transpose_mulVec M z w
    rw [hwe] at hbil
    have hbil' : lam * dotProduct w z = dotProduct w (M.mulVec z) := by
      simpa [dotProduct_smul, dotProduct_comm, smul_eq_mul] using hbil
    have hwz : 0 < dotProduct w z := dotProduct_pos_of_strictlyPositive hw.1 hz
    refine ⟨lam, ?_, hs⟩
    nlinarith [hleft]

theorem irreducibleMetzler_zeroSpectralBound_iff_criticalCertificate
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : IsMetzler M)
    (hirr : HasIrreducibleNonnegativeShift M) :
    IsRealSpectralBound M 0 ↔ CriticalCertificate M := by
  constructor
  · intro hs
    obtain ⟨v, hv, heig⟩ :=
      (irreducibleMetzler_isRealSpectralBound_iff_positiveEigenvector
        M hM hirr 0).mp hs
    exact ⟨v, hv.1, by simpa using heig⟩
  · rintro ⟨v, hv, heig⟩
    apply positiveEigenvector_isRealSpectralBound hM hv
    simpa using heig

theorem irreducibleMetzler_negativeSpectralBound_iff_extinctionCertificate
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : IsMetzler M)
    (hirr : HasIrreducibleNonnegativeShift M) :
    HasNegativeRealSpectralBound M ↔ ExtinctionCertificate M := by
  constructor
  · rintro ⟨lam, hlam, hs⟩
    obtain ⟨v, hv, heig⟩ :=
      (irreducibleMetzler_isRealSpectralBound_iff_positiveEigenvector
        M hM hirr lam).mp hs
    refine ⟨v, hv.1, ?_⟩
    intro i
    rw [heig]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_neg_of_neg_of_pos hlam (hv.1 i)
  · rintro ⟨z, hz, hMz⟩
    obtain ⟨lam, v, hv, heig, hs⟩ :=
      irreducibleMetzler_exists_realSpectralBound M hM hirr
    obtain ⟨w, hw, hwe⟩ :=
      irreducibleMetzler_positiveLeftEigenvector_at_spectralBound M hM hirr hs
    have hleft : dotProduct w (M.mulVec z) < 0 :=
      dotProduct_neg_of_positive_negative hw.1 hMz
    have hbil := Matrix.dotProduct_transpose_mulVec M z w
    rw [hwe] at hbil
    have hbil' : lam * dotProduct w z = dotProduct w (M.mulVec z) := by
      simpa [dotProduct_smul, dotProduct_comm, smul_eq_mul] using hbil
    have hwz : 0 < dotProduct w z := dotProduct_pos_of_strictlyPositive hw.1 hz
    refine ⟨lam, ?_, hs⟩
    nlinarith [hleft]

/-- Source-faithful dynamical autocatalysis at arbitrary nonnegative
degradation: positive real spectral bound is exactly the strict projective
upper-bound certificate.  Source connectivity, rather than an opaque matrix
irreducibility premise, supplies Perron--Frobenius. -/
theorem sourceNetwork_dynamicalAutocatalysis_iff_degradationCertificate
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (rs : List (UnaryReaction ι)) (d : ι → ℝ)
    (hrs : ∀ r ∈ rs, NonnegativeReaction r)
    (hsource : SourceIrreducible rs) :
    (NonnegativeVector d ∧
      HasPositiveRealSpectralBound
        (degradedMatrix (reactionPart rs) d)) ↔
    (NonnegativeVector d ∧
      ∃ v, StrictlyPositive v ∧
        ∀ i, d i < projectiveDegradation (reactionPart rs) v i) := by
  have hA : IsMetzler (reactionPart rs) := by
    intro i j hij
    exact reactionPart_offDiag_nonneg rs hrs hij
  have hM : IsMetzler (degradedMatrix (reactionPart rs) d) :=
    degradedMatrix_isMetzler hA d
  have hirr := sourceIrreducible_hasIrreducibleNonnegativeShift rs d hrs hsource
  rw [irreducibleMetzler_positiveSpectralBound_iff_growthCertificate _ hM hirr,
    growthCertificate_degraded_iff_projective_lt]

/-- Source-faithful strict extinction region at arbitrary nonnegative
degradation, in explicit projective coordinates. -/
theorem sourceNetwork_extinction_iff_degradationCertificate
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (rs : List (UnaryReaction ι)) (d : ι → ℝ)
    (hrs : ∀ r ∈ rs, NonnegativeReaction r)
    (hsource : SourceIrreducible rs) :
    (NonnegativeVector d ∧
      HasNegativeRealSpectralBound
        (degradedMatrix (reactionPart rs) d)) ↔
    (NonnegativeVector d ∧
      ∃ v, StrictlyPositive v ∧
        ∀ i, projectiveDegradation (reactionPart rs) v i < d i) := by
  have hA : IsMetzler (reactionPart rs) := by
    intro i j hij
    exact reactionPart_offDiag_nonneg rs hrs hij
  have hM : IsMetzler (degradedMatrix (reactionPart rs) d) :=
    degradedMatrix_isMetzler hA d
  have hirr := sourceIrreducible_hasIrreducibleNonnegativeShift rs d hrs hsource
  rw [irreducibleMetzler_negativeSpectralBound_iff_extinctionCertificate _ hM hirr,
    extinctionCertificate_degraded_iff_projective_gt]

/-- The exact physical critical boundary derived entirely from the reaction
list, nonnegative rates, and source strong connectivity. -/
theorem sourceNetwork_arbitraryDegradationSpectralCriticalBoundary
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (rs : List (UnaryReaction ι)) (d : ι → ℝ)
    (hrs : ∀ r ∈ rs, NonnegativeReaction r)
    (hsource : SourceIrreducible rs) :
    IrreduciblePhysicalSpectralState (reactionPart rs) d 0 ↔
      ∃ v, NormalizedPositive v ∧
        NonnegativeVector (projectiveDegradation (reactionPart rs) v) ∧
        d = projectiveDegradation (reactionPart rs) v := by
  exact sourceNetwork_irreducibleCriticalBoundary_iff rs d hrs
    (sourceIrreducible_hasIrreducibleNonnegativeShift rs d hrs hsource)

/-- The shifted projective parametrization at every prescribed real spectral
bound, again with source connectivity as the only irreducibility input. -/
theorem sourceNetwork_arbitraryDegradationSpectralState
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (rs : List (UnaryReaction ι)) (d : ι → ℝ) (lam : ℝ)
    (hrs : ∀ r ∈ rs, NonnegativeReaction r)
    (hsource : SourceIrreducible rs) :
    IrreduciblePhysicalSpectralState (reactionPart rs) d lam ↔
      ∃ v, NormalizedPositive v ∧
        NonnegativeVector
          (shiftedProjectiveDegradation (reactionPart rs) v lam) ∧
        d = shiftedProjectiveDegradation (reactionPart rs) v lam := by
  exact sourceNetwork_irreducibleSpectralState_iff rs d lam hrs
    (sourceIrreducible_hasIrreducibleNonnegativeShift rs d hrs hsource)

end DegradationControl
