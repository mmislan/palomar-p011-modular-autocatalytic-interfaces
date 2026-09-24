import proofs.AutocatalyticCS.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
The strict feasibility test used for autocatalysis can be checked over the
rationals without changing its real meaning.  Nonnegative witnesses are
represented by `NNRat`/`NNReal`, so density is used in the correct relative
topology and never perturbs a zero coordinate to a negative one.
-/

namespace AutocatalyticCS

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def ExactSemipositive (A : Matrix ι ι ℚ) : Prop :=
  ∃ v : ι → NNRat, ∀ i, 0 < ∑ j, A i j * (v j : ℚ)

def RealSemipositive (A : Matrix ι ι ℚ) : Prop :=
  ∃ v : ι → NNReal, ∀ i, 0 < ∑ j, (A i j : ℝ) * (v j : ℝ)

/-- A positive exact certificate is just a finite nonnegative rational vector;
verification consists entirely of rational arithmetic. -/
structure PositiveSemipositivityCertificate (A : Matrix ι ι ℚ) where
  vector : ι → NNRat
  verifies : ∀ i, 0 < ∑ j, A i j * (vector j : ℚ)

/-- A Gordan--Stiemke obstruction.  Every field is checked using finite exact
rational sums and comparisons. -/
structure NegativeSemipositivityCertificate (A : Matrix ι ι ℚ) where
  vector : ι → NNRat
  positive : ∃ i, 0 < (vector i : ℚ)
  verifies : ∀ j, ∑ i, A i j * (vector i : ℚ) ≤ 0

omit [DecidableEq ι] [Nonempty ι] in
theorem exactSemipositive_iff_certificate (A : Matrix ι ι ℚ) :
    ExactSemipositive A ↔ Nonempty (PositiveSemipositivityCertificate A) := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨⟨v, hv⟩⟩
  · rintro ⟨certificate⟩
    exact ⟨certificate.vector, certificate.verifies⟩

omit [DecidableEq ι] [Nonempty ι] in
theorem negativeCertificate_refutes_exactSemipositive (A : Matrix ι ι ℚ)
    (certificate : NegativeSemipositivityCertificate A) :
    ¬ ExactSemipositive A := by
  rintro ⟨v, hv⟩
  let lhs : ℚ := ∑ i, (certificate.vector i : ℚ) *
    (∑ j, A i j * (v j : ℚ))
  have hlhs : 0 < lhs := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (certificate.vector i).property (hv i).le
    · rcases certificate.positive with ⟨i, hi⟩
      exact ⟨i, Finset.mem_univ _, mul_pos hi (hv i)⟩
  have hrearrange : lhs = ∑ j, (v j : ℚ) *
      (∑ i, A i j * (certificate.vector i : ℚ)) := by
    simp only [lhs, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrhs : (∑ j, (v j : ℚ) *
      (∑ i, A i j * (certificate.vector i : ℚ))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    exact mul_nonpos_of_nonneg_of_nonpos (v j).property (certificate.verifies j)
  rw [hrearrange] at hlhs
  exact (not_lt_of_ge hrhs) hlhs

omit [DecidableEq ι] in
theorem semipositive_iff_exactSemipositive (A : Matrix ι ι ℚ) :
    Semipositive A ↔ ExactSemipositive A := by
  constructor
  · rintro ⟨v, hvnonneg, _hvne, hv⟩
    refine ⟨fun i => ⟨v i, hvnonneg i⟩, ?_⟩
    simpa using hv
  · rintro ⟨v, hv⟩
    refine ⟨fun i => (v i : ℚ), fun i => (v i).property, ?_, ?_⟩
    · intro hzero
      let i : ι := Classical.choice inferInstance
      have hi := hv i
      have hvzero : ∀ j, (v j : ℚ) = 0 := fun j => congrFun hzero j
      simp [hvzero] at hi
    · simpa using hv

private def nnratToNNReal (q : NNRat) : NNReal :=
  ⟨((q : ℚ) : ℝ), Rat.cast_nonneg.2 q.property⟩

@[simp] private theorem coe_nnratToNNReal (q : NNRat) :
    (nnratToNNReal q : ℝ) = ((q : ℚ) : ℝ) := rfl

omit [DecidableEq ι] [Nonempty ι] in
private theorem ratCast_finsetSum (f : ι → ℚ) :
    ((∑ i, f i : ℚ) : ℝ) = ∑ i, (f i : ℝ) :=
  map_sum (Rat.castHom ℝ) f Finset.univ

private theorem denseRange_nnratCast :
    DenseRange nnratToNNReal := by
  apply dense_of_exists_between
  intro a b hab
  rcases (NNReal.lt_iff_exists_rat_btwn a b).1 hab with ⟨q, hq, haq, hqb⟩
  refine Set.exists_range_iff.2 ⟨⟨q, hq⟩, ?_⟩
  have hcast : Real.toNNReal (q : ℝ) = nnratToNNReal ⟨q, hq⟩ := by
    apply Subtype.ext
    exact Real.coe_toNNReal _ (Rat.cast_nonneg.2 hq)
  rw [← hcast]
  exact ⟨haq, hqb⟩

omit [DecidableEq ι] [Nonempty ι] in
theorem exactSemipositive_iff_realSemipositive (A : Matrix ι ι ℚ) :
    ExactSemipositive A ↔ RealSemipositive A := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨fun j => nnratToNNReal (v j), ?_⟩
    intro i
    change 0 < ∑ j, (A i j : ℝ) * ((v j : ℚ) : ℝ)
    simp_rw [← Rat.cast_mul]
    rw [← ratCast_finsetSum]
    exact Rat.cast_pos.mpr (hv i)
  · rintro ⟨v, hv⟩
    let feasible : Set (ι → NNReal) :=
      {w | ∀ i, 0 < ∑ j, (A i j : ℝ) * (w j : ℝ)}
    have hcontinuous : ∀ i, Continuous fun w : ι → NNReal =>
        ∑ j, (A i j : ℝ) * (w j : ℝ) := by
      intro i
      exact continuous_finsetSum Finset.univ fun j _ =>
        continuous_const.mul (continuous_subtype_val.comp (continuous_apply j))
    have hopen : IsOpen feasible := by
      rw [show feasible = ⋂ i, {w | 0 < ∑ j, (A i j : ℝ) * (w j : ℝ)} by
        ext w
        simp [feasible]]
      exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (hcontinuous i)
    have hdense : DenseRange (fun q : ι → NNRat => fun j => nnratToNNReal (q j)) := by
      simpa only [Pi.map_apply] using
        DenseRange.piMap (fun _ : ι => denseRange_nnratCast)
    obtain ⟨q, hq⟩ := hdense.exists_mem_open hopen ⟨v, hv⟩
    refine ⟨q, ?_⟩
    intro i
    have hi := hq i
    change 0 < ∑ j, (A i j : ℝ) * ((q j : ℚ) : ℝ) at hi
    simp_rw [← Rat.cast_mul] at hi
    rw [← ratCast_finsetSum] at hi
    exact Rat.cast_pos.mp hi

omit [DecidableEq ι] in
theorem semipositive_iff_realSemipositive (A : Matrix ι ι ℚ) :
    Semipositive A ↔ RealSemipositive A :=
  (semipositive_iff_exactSemipositive A).trans
    (exactSemipositive_iff_realSemipositive A)

end AutocatalyticCS
