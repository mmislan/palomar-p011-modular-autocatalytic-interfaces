import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs

/-! Minimal explicit-catalysis semantics used by the extraction theorem. -/

namespace AutocatalyticCS

structure ReactionNetwork (X R : Type*) where
  reactant : X → R → ℕ
  product : X → R → ℕ

namespace ReactionNetwork

def net {X R : Type*} (Q : ReactionNetwork X R) (x : X) (r : R) : ℤ :=
  (Q.product x r : ℤ) - (Q.reactant x r : ℤ)

end ReactionNetwork

variable {X R : Type*} [DecidableEq X] [DecidableEq R]

structure ChildSelection (Q : ReactionNetwork X R) where
  species : Finset X
  reactions : Finset R
  assign : {x // x ∈ species} ≃ {r // r ∈ reactions}
  reactant_match : ∀ x, 0 < Q.reactant x.1 (assign x).1

namespace ChildSelection

variable {Q : ReactionNetwork X R}

def matrix (κ : ChildSelection Q) : Matrix κ.species κ.species ℤ :=
  fun x y => Q.net x.1 (κ.assign y).1

def Restricts (κ₁ κ₂ : ChildSelection Q) : Prop :=
  κ₁.species ⊆ κ₂.species ∧
  κ₁.reactions ⊆ κ₂.reactions ∧
  ∀ (x₁ : {x // x ∈ κ₁.species}) (x₂ : {x // x ∈ κ₂.species}),
    x₁.1 = x₂.1 → (κ₁.assign x₁).1 = (κ₂.assign x₂).1

end ChildSelection

def Semipositive {ι : Type*} [Fintype ι] (A : Matrix ι ι ℚ) : Prop :=
  ∃ v : ι → ℚ,
    (∀ i, 0 ≤ v i) ∧
    v ≠ 0 ∧
    ∀ i, 0 < A.mulVec v i

def ChildSelection.Autocatalytic {Q : ReactionNetwork X R} (κ : ChildSelection Q) : Prop :=
  Semipositive (fun i j => (κ.matrix i j : ℚ))

/- Two networks may have identical net stoichiometry while having different
reactant incidence.  This predicate keeps that distinction explicit. -/
def NetEquivalent (Q₁ Q₂ : ReactionNetwork X R) : Prop :=
  ∀ x r, Q₁.net x r = Q₂.net x r

end AutocatalyticCS
