import proofs.DegradationControl.TypeII2
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

namespace DegradationControl

/-- The five source-classified families of finite diluted autocatalytic cores. -/
inductive DilutedCoreType
  | typeI
  | typeII (loopCount : Nat)
  | typeIII
  | typeIV
  | typeV
  deriving DecidableEq, Repr

/-- A rational finite next-generation realization tagged by its classified
core family.  Rational input is the exact-computation regime used by the atlas
algorithm. -/
structure RationalClassifiedCore where
  speciesCount : Nat
  kind : DilutedCoreType
  nextGeneration : Matrix (Fin speciesCount) (Fin speciesCount) ℚ

def typeICore (K : Matrix (Fin n) (Fin n) ℚ) : RationalClassifiedCore :=
  ⟨n, .typeI, K⟩

def typeIICore (loopCount : Nat) (K : Matrix (Fin n) (Fin n) ℚ) :
    RationalClassifiedCore :=
  ⟨n, .typeII loopCount, K⟩

def typeIIICore (K : Matrix (Fin n) (Fin n) ℚ) : RationalClassifiedCore :=
  ⟨n, .typeIII, K⟩

def typeIVCore (K : Matrix (Fin n) (Fin n) ℚ) : RationalClassifiedCore :=
  ⟨n, .typeIV, K⟩

def typeVCore (K : Matrix (Fin n) (Fin n) ℚ) : RationalClassifiedCore :=
  ⟨n, .typeV, K⟩

@[simp] theorem typeIICore_matrix (loopCount : Nat)
    (K : Matrix (Fin n) (Fin n) ℚ) :
    (typeIICore loopCount K).nextGeneration = K := rfl

/-- Exact characteristic polynomial used by the branch-safe finite atlas. -/
noncomputable def RationalClassifiedCore.controlPolynomial
    (C : RationalClassifiedCore) : Polynomial ℚ :=
  C.nextGeneration.charpoly

/-- Every evaluation used by the atlas is a finite signed permutation sum.
This is the exact cycle-cover enumerator; zero entries automatically remove
non-covers. -/
theorem charpoly_eval_cycleCover
    {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n R) (t : R) :
    K.charpoly.eval t =
      ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ •
        ∏ i, (Matrix.scalar n t - K) (σ i) i := by
  rw [Matrix.eval_charpoly, Matrix.det_apply]

/-- Coverage theorem: the same finite cycle-cover polynomial is available for
every member of every classified family, including arbitrary Type II loop
count. -/
theorem classifiedCore_controlPolynomial_eval (C : RationalClassifiedCore) (t : ℚ) :
    C.controlPolynomial.eval t =
      ∑ σ : Equiv.Perm (Fin C.speciesCount), Equiv.Perm.sign σ •
        ∏ i, (Matrix.scalar (Fin C.speciesCount) t - C.nextGeneration) (σ i) i := by
  exact charpoly_eval_cycleCover C.nextGeneration t

end DegradationControl
