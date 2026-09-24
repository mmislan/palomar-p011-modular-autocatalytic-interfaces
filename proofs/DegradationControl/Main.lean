import proofs.DegradationControl.RobustInterval
import proofs.DegradationControl.GaugePositivity
import proofs.DegradationControl.PerronExistence
import proofs.DegradationControl.PartialActuation

namespace DegradationControl

/-- Legacy algebraic form of the arbitrary-degradation critical boundary.
The bare spectral form, with Perron existence proved rather than assumed, is
the zero-spectral-bound component of `sourceNetwork_arbitraryDegradationRegions`
below. -/
theorem arbitraryDegradationCriticalBoundary
    [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) :
    AlgebraicCritical A d ↔
      ∃ v, NormalizedPositive v ∧
        NonnegativeVector (projectiveDegradation A v) ∧
        d = projectiveDegradation A v :=
  algebraicCritical_iff_projective A d

/-- Source-derived networks are Metzler away from the diagonal for every
species-wise degradation vector. -/
theorem sourceFaithfulArbitraryDegradation_isMetzler
    [DecidableEq ι]
    (rs : List (UnaryReaction ι)) (d : ι → ℝ)
    (hrs : ∀ r ∈ rs, NonnegativeReaction r)
    {i j : ι} (hij : i ≠ j) :
    0 ≤ networkMatrix rs d i j :=
  networkMatrix_offDiag_nonneg rs d hrs hij

/-- The exact finite atlas covers every tagged classified core family by one
finite signed cycle-cover polynomial. -/
theorem arbitraryDegradationFiniteAtlas
    (C : RationalClassifiedCore) (t : ℚ) :
    C.controlPolynomial.eval t =
      ∑ σ : Equiv.Perm (Fin C.speciesCount), Equiv.Perm.sign σ •
        ∏ i, (Matrix.scalar (Fin C.speciesCount) t - C.nextGeneration) (σ i) i :=
  classifiedCore_controlPolynomial_eval C t

/-- The corrected scientific headline.  For a nonnegative source-faithful
reaction list whose source graph is strongly connected, the entire arbitrary
nonnegative degradation region is characterized in projective coordinates:
strict growth lies below `Av/v`, the zero-spectral-bound boundary is its exact
normalized image, and strict extinction lies above it.  No matrix-level
irreducibility or positive eigenmode is assumed by the caller. -/
theorem sourceNetwork_arbitraryDegradationRegions
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (rs : List (UnaryReaction ι)) (d : ι → ℝ)
    (hrs : ∀ r ∈ rs, NonnegativeReaction r)
    (hsource : SourceIrreducible rs) :
    ((NonnegativeVector d ∧
        HasPositiveRealSpectralBound
          (degradedMatrix (reactionPart rs) d)) ↔
      (NonnegativeVector d ∧
        ∃ v, StrictlyPositive v ∧
          ∀ i, d i < projectiveDegradation (reactionPart rs) v i)) ∧
    (IrreduciblePhysicalSpectralState (reactionPart rs) d 0 ↔
      ∃ v, NormalizedPositive v ∧
        NonnegativeVector (projectiveDegradation (reactionPart rs) v) ∧
        d = projectiveDegradation (reactionPart rs) v) ∧
    ((NonnegativeVector d ∧
        HasNegativeRealSpectralBound
          (degradedMatrix (reactionPart rs) d)) ↔
      (NonnegativeVector d ∧
        ∃ v, StrictlyPositive v ∧
          ∀ i, projectiveDegradation (reactionPart rs) v i < d i)) := by
  exact ⟨
    sourceNetwork_dynamicalAutocatalysis_iff_degradationCertificate
      rs d hrs hsource,
    sourceNetwork_arbitraryDegradationSpectralCriticalBoundary
      rs d hrs hsource,
    sourceNetwork_extinction_iff_degradationCertificate
      rs d hrs hsource⟩

end DegradationControl
