import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Sum
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

/-!
# Exact interfaces for modular autocatalytic networks
This draft covers literature questions 13, 14 and 15: composition rules,
exact child-selection core reconstruction, and diluted degradation onset.
The attained maximum amplification factor and its threshold-indexed price
profile are exposed for reaction addition, aggregation, and coupling.
-/

namespace MAFComposition
open scoped BigOperators
variable {ι ζ κ ρ : Type} [Fintype ι] [Fintype ζ] [Fintype κ] [Fintype ρ]
def ExactThreshold (F : ℝ → Prop) (a : ℝ) : Prop :=
  F a ∧ ∀ q, F q → q ≤ a

-- N1: A → B and B → 4A.

def N1Feasible (q : ℝ) : Prop :=
  ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ (x ≠ 0 ∨ y ≠ 0) ∧
    q * x ≤ 4 * y ∧ q * y ≤ x

-- N2: A → 4B and B → A.

def N2Feasible (q : ℝ) : Prop :=
  ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ (x ≠ 0 ∨ y ≠ 0) ∧
    q * x ≤ y ∧ q * y ≤ 4 * x

def N1N1Feasible (q : ℝ) : Prop :=
  ∃ a b c d : ℝ,
    0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧
    (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) ∧
    q * (a + c) ≤ 4 * (b + d) ∧ q * (b + d) ≤ a + c

def N2N1Feasible (q : ℝ) : Prop :=
  ∃ a b c d : ℝ,
    0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧
    (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) ∧
    q * (a + c) ≤ b + 4 * d ∧ q * (b + d) ≤ 4 * a + c

def weightedColumn (p : ι → ℝ) (M : ι → κ → ℝ) (r : κ) : ℝ :=
  ∑ i, p i * M i r

def StrictObstruction (A B : ι → κ → ℝ) (q : ℝ) (p : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∀ r, weightedColumn p B r < q * weightedColumn p A r

def parallelColumns (M₁ : ι → κ → ℝ) (M₂ : ι → ρ → ℝ) :
    ι → Sum κ ρ → ℝ :=
  fun i r => Sum.elim (M₁ i) (M₂ i) r

def singletonColumn (v : ι → ℝ) : ι → Unit → ℝ := fun i _ => v i

structure Network (ι κ : Type) where
  input : Matrix ι κ ℝ
  output : Matrix ι κ ℝ

def Network.InputNonnegative (N : Network ι κ) : Prop :=
  ∀ i r, 0 ≤ N.input i r

def Network.FeasibleAt (N : Network ι κ) (q : ℝ) : Prop :=
  ∃ x : κ → ℝ, (∀ r, 0 ≤ x r) ∧ x ≠ 0 ∧
    ∀ i, q * N.input.mulVec x i ≤ N.output.mulVec x i

def Network.IsMAF (N : Network ι κ) (a : ℝ) : Prop :=
  N.FeasibleAt a ∧ ∀ q, N.FeasibleAt q → q ≤ a

def Network.parallel (N₁ : Network ι κ) (N₂ : Network ι ρ) :
    Network ι (Sum κ ρ) where
  input := parallelColumns N₁.input N₂.input
  output := parallelColumns N₁.output N₂.output

def Network.priceCone (N : Network ι κ) (q : ℝ) : Set (ι → ℝ) :=
  {p | StrictObstruction N.input N.output q p}

def Network.singleReaction (a b : ι → ℝ) : Network ι Unit where
  input := singletonColumn a
  output := singletonColumn b

def Network.addReaction (N : Network ι κ) (a b : ι → ℝ) :
    Network ι (Sum κ Unit) :=
  N.parallel (Network.singleReaction a b)

def reactionHalfspace (a b : ι → ℝ) (q : ℝ) : Set (ι → ℝ) :=
  {p | weightedColumn p (singletonColumn b) () <
    q * weightedColumn p (singletonColumn a) ()}

def VectorNonnegative (v : ι → ℝ) : Prop := ∀ i, 0 ≤ v i

def Matrix.EntrywiseNonnegative (C : Matrix ζ ι ℝ) : Prop :=
  ∀ z i, 0 ≤ C z i

def Network.aggregate (C : Matrix ζ ι ℝ) (N : Network ι κ) : Network ζ κ where
  input := C * N.input
  output := C * N.output

def blockColumns (M₁ : Matrix ι κ ℝ) (M₂ : Matrix ζ ρ ℝ) :
    Matrix (Sum ι ζ) (Sum κ ρ) ℝ
  | Sum.inl i, Sum.inl r => M₁ i r
  | Sum.inr z, Sum.inr s => M₂ z s
  | _, _ => 0

def Network.directSum (N₁ : Network ι κ) (N₂ : Network ζ ρ) :
    Network (Sum ι ζ) (Sum κ ρ) where
  input := blockColumns N₁.input N₂.input
  output := blockColumns N₁.output N₂.output

end MAFComposition
namespace MAFComposition
variable {ι κ : Type} [Fintype ι] [Fintype κ]
theorem reactionEdit
    (N : Network ι κ) (hN : N.InputNonnegative)
    (a b : ι → ℝ) (ha0 : VectorNonnegative a)
    {α β : ℝ} (hα : N.IsMAF α) (hβ : (N.addReaction a b).IsMAF β) :
    α < β ↔
      ¬ ∀ q, α < q → ∃ p, p ∈ N.priceCone q ∩ reactionHalfspace a b q := by
  sorry

theorem aggregate
    {ζ : Type} [Fintype ζ]
    (C : Matrix ζ ι ℝ) (hC : Matrix.EntrywiseNonnegative C)
    (N : Network ι κ) (hN : N.InputNonnegative)
    {a b : ℝ} (ha : N.IsMAF a) (hb : (N.aggregate C).IsMAF b) :
    a < b ↔
      ¬ ∀ q, a < q → ∃ p : ζ → ℝ,
        (∀ z, 0 ≤ p z) ∧ Matrix.vecMul p C ∈ N.priceCone q := by
  sorry

theorem directSum
    {ζ ρ : Type} [Fintype ζ] [Fintype ρ]
    (N₁ : Network ι κ) (N₂ : Network ζ ρ)
    (hA₁ : N₁.InputNonnegative) (hA₂ : N₂.InputNonnegative)
    {a b : ℝ} (ha : N₁.IsMAF a) (hb : N₂.IsMAF b) :
    (N₁.directSum N₂).IsMAF (max a b) := by
  sorry

theorem parallel
    {ρ : Type} [Fintype ρ]
    (N₁ : Network ι κ) (N₂ : Network ι ρ)
    (hA₁ : N₁.InputNonnegative) (hA₂ : N₂.InputNonnegative)
    {a b c : ℝ} (ha : N₁.IsMAF a) (hb : N₂.IsMAF b)
    (hc : (N₁.parallel N₂).IsMAF c) :
    max a b < c ↔
      ¬ ∀ q, max a b < q → ∃ p, p ∈ N₁.priceCone q ∩ N₂.priceCone q := by
  sorry

theorem scalarNoncompositionality :
    ExactThreshold N1Feasible 2 ∧ ExactThreshold N2Feasible 2 ∧
      ExactThreshold N1N1Feasible 2 ∧ ExactThreshold N2N1Feasible 4 := by
  sorry

end MAFComposition
namespace DegradationControl
open scoped BigOperators
structure UnaryReaction (ι : Type*) where
  substrate : ι
  products : ι → ℝ
  rate : ℝ

def UnaryReaction.matrix [DecidableEq ι] (r : UnaryReaction ι) : Matrix ι ι ℝ :=
  fun i j => if j = r.substrate then
    r.rate * (r.products i - if i = r.substrate then 1 else 0)
  else 0

def degradationMatrix [DecidableEq ι] (d : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => if i = j then -d i else 0

def reactionPart [DecidableEq ι] : List (UnaryReaction ι) → Matrix ι ι ℝ
  | [] => 0
  | r :: rs => r.matrix + reactionPart rs

def NonnegativeReaction (r : UnaryReaction ι) : Prop :=
  0 ≤ r.rate ∧ ∀ i, 0 ≤ r.products i

noncomputable def sourceAdjacency [DecidableEq ι]
    (rs : List (UnaryReaction ι)) : Matrix ι ι ℝ :=
  fun i j => if i = j then 1 else max (reactionPart rs i j) 0

def SourceIrreducible [DecidableEq ι]
    (rs : List (UnaryReaction ι)) : Prop :=
  Matrix.IsIrreducible (sourceAdjacency rs)

def StrictlyPositive (v : ι → ℝ) : Prop := ∀ i, 0 < v i

def StrictlyNegative (v : ι → ℝ) : Prop := ∀ i, v i < 0

def ExtinctionCertificate [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) : Prop :=
  ∃ v, StrictlyPositive v ∧ StrictlyNegative (Matrix.mulVec M v)

def degradedMatrix [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) : Matrix ι ι ℝ :=
  A + degradationMatrix d

noncomputable def projectiveDegradation [Fintype ι]
    (A : Matrix ι ι ℝ) (v : ι → ℝ) (i : ι) : ℝ :=
  Matrix.mulVec A v i / v i

def NonnegativeVector (v : ι → ℝ) : Prop := ∀ i, 0 ≤ v i

def NormalizedPositive [Fintype ι] (v : ι → ℝ) : Prop :=
  StrictlyPositive v ∧ ∑ i, v i = 1

def IsMetzler [DecidableEq ι] (M : Matrix ι ι ℝ) : Prop :=
  ∀ i j, i ≠ j → 0 ≤ M i j

def complexify (M : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  M.map Complex.ofReal

def IsRealSpectralBound [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (lam : ℝ) : Prop :=
  Module.End.HasEigenvalue (Matrix.toLin' (complexify M)) (lam : ℂ) ∧
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (complexify M)) μ → μ.re ≤ lam

def IrreduciblePhysicalSpectralState [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) (lam : ℝ) : Prop :=
  NonnegativeVector d ∧ IsRealSpectralBound (degradedMatrix A d) lam

def HasPositiveRealSpectralBound [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : Prop :=
  ∃ lam, 0 < lam ∧ IsRealSpectralBound M lam

def HasNegativeRealSpectralBound [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : Prop :=
  ∃ lam, lam < 0 ∧ IsRealSpectralBound M lam

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
  sorry

variable {U S : Type*} [Fintype U] [Fintype S] [DecidableEq U] [DecidableEq S]
def unactuatedBlock (A : Matrix (U ⊕ S) (U ⊕ S) ℝ) : Matrix U U ℝ :=
  A.submatrix Sum.inl Sum.inl

def SupportedActuatedDegradation (d : (U ⊕ S) → ℝ) : Prop :=
  NonnegativeVector d ∧ ∀ i : U, d (Sum.inl i) = 0

def PartiallyStabilizable (A : Matrix (U ⊕ S) (U ⊕ S) ℝ) : Prop :=
  ∃ d, SupportedActuatedDegradation d ∧
    ExtinctionCertificate (degradedMatrix A d)

theorem partialActuation_stabilizable_iff_unactuatedCertificate
    (A : Matrix (U ⊕ S) (U ⊕ S) ℝ) (hA : IsMetzler A) :
    PartiallyStabilizable A ↔ ExtinctionCertificate (unactuatedBlock A) := by
  sorry

end DegradationControl
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

variable {Q : ReactionNetwork X R}
structure IndexedMatching (Q : ReactionNetwork X R) where
  card : Nat
  left : Fin card → X
  right : Fin card → R
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  reactant_edge : ∀ i, 0 < Q.reactant (left i) (right i)

namespace IndexedMatching

def species (E : IndexedMatching Q) : Finset X :=
  Finset.univ.image E.left

def reactions (E : IndexedMatching Q) : Finset R :=
  Finset.univ.image E.right

private def leftEmbedding (E : IndexedMatching Q) : Fin E.card ↪ X :=
  ⟨E.left, E.left_injective⟩

private def rightEmbedding (E : IndexedMatching Q) : Fin E.card ↪ R :=
  ⟨E.right, E.right_injective⟩

private def leftRangeEquiv (E : IndexedMatching Q) :
    {x // x ∈ Set.range E.left} ≃ {x // x ∈ E.species} :=
  Equiv.subtypeEquivRight fun x => by simp [species]

private def rightRangeEquiv (E : IndexedMatching Q) :
    {r // r ∈ Set.range E.right} ≃ {r // r ∈ E.reactions} :=
  Equiv.subtypeEquivRight fun r => by simp [reactions]

private def leftIndexEquiv (E : IndexedMatching Q) :
    {x // x ∈ E.species} ≃ Fin E.card :=
  E.leftRangeEquiv.symm |>.trans E.leftEmbedding.toEquivRange.symm

private def rightIndexEquiv (E : IndexedMatching Q) :
    {r // r ∈ E.reactions} ≃ Fin E.card :=
  E.rightRangeEquiv.symm |>.trans E.rightEmbedding.toEquivRange.symm

def assign (E : IndexedMatching Q) :
    {x // x ∈ E.species} ≃ {r // r ∈ E.reactions} :=
  E.leftIndexEquiv |>.trans E.rightIndexEquiv.symm

omit [DecidableEq R] in
private theorem leftIndex_symm_val (E : IndexedMatching Q) (i : Fin E.card) :
    ((E.leftIndexEquiv).symm i).1 = E.left i := by
  change (E.leftEmbedding.toEquivRange i).1 = E.left i
  rfl

omit [DecidableEq X] in
private theorem rightIndex_symm_val (E : IndexedMatching Q) (i : Fin E.card) :
    ((E.rightIndexEquiv).symm i).1 = E.right i := by
  change (E.rightEmbedding.toEquivRange i).1 = E.right i
  rfl

theorem assign_index (E : IndexedMatching Q) (i : Fin E.card) :
    (E.assign ((E.leftIndexEquiv).symm i)).1 = E.right i := by
  simp [assign, E.rightIndex_symm_val]

def toChildSelection (E : IndexedMatching Q) : ChildSelection Q where
  species := E.species
  reactions := E.reactions
  assign := E.assign
  reactant_match := by
    intro x
    let i := E.leftIndexEquiv x
    have hleft : x.1 = E.left i := by
      simpa [i] using E.leftIndex_symm_val i
    have hright : (E.assign x).1 = E.right i := by
      simpa [i] using E.assign_index i
    simpa [hleft, hright] using E.reactant_edge i

end IndexedMatching
def MatchingEdgesOK (Q : ReactionNetwork X R) (edges : List (X × R)) : Prop :=
  (edges.map Prod.fst).Nodup ∧
  (edges.map Prod.snd).Nodup ∧
  ∀ e ∈ edges, 0 < Q.reactant e.1 e.2

def matchingEdgesValid (Q : ReactionNetwork X R) (edges : List (X × R)) : Bool :=
  decide (edges.map Prod.fst).Nodup &&
    decide (edges.map Prod.snd).Nodup &&
    edges.all fun e => decide (0 < Q.reactant e.1 e.2)

theorem matchingEdgesValid_eq_true_iff (Q : ReactionNetwork X R)
    (edges : List (X × R)) :
    matchingEdgesValid Q edges = true ↔ MatchingEdgesOK Q edges := by
  simp [matchingEdgesValid, MatchingEdgesOK, and_assoc]

def IndexedMatching.ofValidEdges (Q : ReactionNetwork X R) (edges : List (X × R))
    (h : matchingEdgesValid Q edges = true) : IndexedMatching Q := by
  have hok := (matchingEdgesValid_eq_true_iff Q edges).1 h
  exact
    { card := edges.length
      left := fun i => (edges.get i).1
      right := fun i => (edges.get i).2
      left_injective := by
        intro i j hij
        let i' : Fin (edges.map Prod.fst).length := ⟨i, by simp⟩
        let j' : Fin (edges.map Prod.fst).length := ⟨j, by simp⟩
        have heq : i' = j' := hok.1.get_inj_iff.mp (by simpa [i', j'] using hij)
        have hv : i'.val = j'.val := congrArg (fun z => z.val) heq
        exact Fin.ext (show i.val = j.val from hv)
      right_injective := by
        intro i j hij
        let i' : Fin (edges.map Prod.snd).length := ⟨i, by simp⟩
        let j' : Fin (edges.map Prod.snd).length := ⟨j, by simp⟩
        have heq : i' = j' := hok.2.1.get_inj_iff.mp (by simpa [i', j'] using hij)
        have hv : i'.val = j'.val := congrArg (fun z => z.val) heq
        exact Fin.ext (show i.val = j.val from hv)
      reactant_edge := fun i => hok.2.2 (edges.get i) (edges.get_mem i) }

def IndexedMatching.edgeList (E : IndexedMatching Q) : List (X × R) :=
  List.ofFn fun i => (E.left i, E.right i)

def IndexedMatching.edgeFinset (E : IndexedMatching Q) : Finset (X × R) :=
  E.edgeList.toFinset

section Paths
variable {V : Type*} [DecidableEq V]
def directPathsAux (next : V → List V) (target : V → Bool) :
    Nat → List V → V → List (List V)
  | 0, _visited, current =>
      if target current then [[current]] else []
  | fuel + 1, visited, current =>
      if target current then [[current]]
      else
        (next current).filter (fun successor => successor ∉ current :: visited)
          |>.flatMap fun successor =>
            (directPathsAux next target fuel (current :: visited) successor).map
              (current :: ·)

def directPaths [Fintype V] (next : V → List V) (target : V → Bool)
    (start : V) : List (List V) :=
  directPathsAux next target (Fintype.card V) [] start

def directBoundaryPaths [Fintype V] (next : V → List V) (target : V → Bool)
    (starts : List V) : List (List V) :=
  starts.flatMap (directPaths next target)

def OrderedPathCompatible (p : List V) (pack : List (List V)) : Bool :=
  pack.all fun q => decide (Disjoint p.toFinset q.toFinset)

def directOrderedPathPacks : List (List V) → List (List (List V))
  | [] => [[]]
  | p :: paths =>
      let rest := directOrderedPathPacks paths
      rest ++ (rest.filter (OrderedPathCompatible p)).map (p :: ·)

def directBoundaryPathPacks [Fintype V] (next : V → List V)
    (target : V → Bool) (starts : List V) : List (List (List V)) :=
  directOrderedPathPacks (directBoundaryPaths next target starts)

end Paths
def forwardEdges : List (X ⊕ R) → List (X × R)
  | Sum.inl x :: Sum.inr r :: tail => (x, r) :: forwardEdges (Sum.inr r :: tail)
  | _ :: tail => forwardEdges tail
  | [] => []

def backwardEdges : List (X ⊕ R) → List (X × R)
  | Sum.inr r :: Sum.inl x :: tail => (x, r) :: backwardEdges (Sum.inl x :: tail)
  | _ :: tail => backwardEdges tail
  | [] => []

def forwardPackEdges (pack : List (List (X ⊕ R))) : List (X × R) :=
  pack.flatMap forwardEdges

def backwardPackEdges (pack : List (List (X ⊕ R))) : List (X × R) :=
  pack.flatMap backwardEdges

def toggledEdges (anchor : IndexedMatching Q) (pack : List (List (X ⊕ R))) :
    List (X × R) :=
  anchor.edgeList.filter (fun e => e ∉ backwardPackEdges pack) ++
    forwardPackEdges pack

def buildPathPackCandidate? (Q : ReactionNetwork X R) (anchor : IndexedMatching Q)
    (pack : List (List (X ⊕ R))) : Option (IndexedMatching Q) :=
  if h : matchingEdgesValid Q (toggledEdges anchor pack) = true then
    some (IndexedMatching.ofValidEdges Q (toggledEdges anchor pack) h)
  else none

def sourceExchangeNext (Q : ReactionNetwork X R) (anchor : IndexedMatching Q)
    (reactionOrder : List R) :
    X ⊕ R → List (X ⊕ R)
  | Sum.inl x =>
      ((reactionOrder.filter fun r => 0 < Q.reactant x r).map Sum.inr).dedup
  | Sum.inr r =>
      (anchor.edgeList.filterMap fun e =>
        if e.2 = r then some (Sum.inl e.1) else none).dedup

def sourceBoundaryStarts (anchor : IndexedMatching Q) (speciesOrder : List X) :
    List (X ⊕ R) :=
  ((speciesOrder.filter fun x => x ∉ anchor.species).map Sum.inl).dedup

def sourceBoundaryTarget (anchor : IndexedMatching Q) : X ⊕ R → Bool
  | Sum.inl _ => false
  | Sum.inr r => decide (r ∉ anchor.reactions)

def sourcePathPacks [Fintype X] [Fintype R] (Q : ReactionNetwork X R)
    (anchor : IndexedMatching Q) (speciesOrder : List X) (reactionOrder : List R) :
    List (List (List (X ⊕ R))) :=
  directBoundaryPathPacks (sourceExchangeNext Q anchor reactionOrder)
    (sourceBoundaryTarget anchor) (sourceBoundaryStarts anchor speciesOrder)

def sourceCandidates [Fintype X] [Fintype R] (Q : ReactionNetwork X R)
    (anchor : IndexedMatching Q) (speciesOrder : List X) (reactionOrder : List R) :
    List (IndexedMatching Q) :=
  (sourcePathPacks Q anchor speciesOrder reactionOrder).filterMap
    (buildPathPackCandidate? Q anchor)

def sourceCandidateEdgeFinsets [Fintype X] [Fintype R]
    (Q : ReactionNetwork X R) (anchor : IndexedMatching Q)
    (speciesOrder : List X) (reactionOrder : List R) :
    List (Finset (X × R)) :=
  (sourceCandidates Q anchor speciesOrder reactionOrder).map
    IndexedMatching.edgeFinset

def reactantGraph (Q : ReactionNetwork X R) : _root_.SimpleGraph (X ⊕ R) where
  Adj u v := match u, v with
    | Sum.inl x, Sum.inr r => 0 < Q.reactant x r
    | Sum.inr r, Sum.inl x => 0 < Q.reactant x r
    | _, _ => False
  symm := ⟨by intro u v; cases u <;> cases v <;> simp_all⟩
  loopless := ⟨by rintro (x | r) h <;> exact h⟩

def IndexedMatching.subgraph (E : IndexedMatching Q) : (reactantGraph Q).Subgraph where
  verts v := match v with
    | Sum.inl x => x ∈ E.species
    | Sum.inr r => r ∈ E.reactions
  Adj u v := match u, v with
    | Sum.inl x, Sum.inr r => ∃ i, E.left i = x ∧ E.right i = r
    | Sum.inr r, Sum.inl x => ∃ i, E.left i = x ∧ E.right i = r
    | _, _ => False
  adj_sub := by
    intro u v h
    cases u with
    | inl x =>
        cases v with
        | inl y => exact h.elim
        | inr r =>
            obtain ⟨i, rfl, rfl⟩ := h
            exact E.reactant_edge i
    | inr r =>
        cases v with
        | inl x =>
            obtain ⟨i, rfl, rfl⟩ := h
            exact E.reactant_edge i
        | inr s => exact h.elim
  edge_vert := by
    intro u v h
    cases u with
    | inl x =>
        cases v with
        | inl y => exact h.elim
        | inr r =>
            obtain ⟨i, rfl, rfl⟩ := h
            change E.left i ∈ E.species
            simp [IndexedMatching.species]
    | inr r =>
        cases v with
        | inl x =>
            obtain ⟨i, rfl, rfl⟩ := h
            change E.right i ∈ E.reactions
            simp [IndexedMatching.reactions]
        | inr s => exact h.elim
  symm := ⟨by
    intro u v h
    cases u <;> cases v <;> exact h⟩

namespace SimpleGraph
open _root_.SimpleGraph
variable {V : Type*} {A : _root_.SimpleGraph V}
def Subgraph.IsUniqueMatching (M : A.Subgraph) : Prop :=
  M.IsMatching ∧ ∀ N : A.Subgraph, N.IsMatching → N.verts = M.verts → N = M

end SimpleGraph
section Minimality
variable {α : Type*} [PartialOrder α] [Finite α]
def IsCore (good : α → Prop) (a : α) : Prop :=
  good a ∧ ∀ ⦃b⦄, b < a → ¬ good b

end Minimality
variable [Fintype X] [Fintype R]
abbrev Subnetwork (X R : Type*) := Finset X × Finset R

def IndexedMatching.underlying (E : IndexedMatching Q) : Subnetwork X R :=
  (E.species, E.reactions)

def AutocatalyticSubnetwork (Q : ReactionNetwork X R)
    (N : Subnetwork X R) : Prop :=
  ∃ E : IndexedMatching Q,
    E.underlying = N ∧ E.toChildSelection.Autocatalytic

def OrdinaryCore (Q : ReactionNetwork X R) (N : Subnetwork X R) : Prop :=
  IsCore (AutocatalyticSubnetwork Q) N

def AutocatalyticEdgeSet (Q : ReactionNetwork X R)
    (edges : Finset (X × R)) : Prop :=
  ∃ E : IndexedMatching Q,
    E.edgeFinset = edges ∧ E.toChildSelection.Autocatalytic

def allSourceCandidateEdgeFinsets (Q : ReactionNetwork X R)
    (anchors : List (IndexedMatching Q))
    (speciesOrder : List X) (reactionOrder : List R) :
    Finset (Finset (X × R)) :=
  (anchors.flatMap fun anchor =>
    sourceCandidateEdgeFinsets Q anchor speciesOrder reactionOrder).toFinset

def IndexedMatching.rationalMatrix (E : IndexedMatching Q) :
    Matrix E.species E.species ℚ :=
  fun i j => (Q.net i.1 (E.assign j).1 : ℚ)

structure PositiveRationalCertificate (E : IndexedMatching Q) where
  vector : E.species → ℚ
  nonnegative : ∀ i, 0 ≤ vector i
  nonzero : vector ≠ 0
  verifies : ∀ i, 0 < E.rationalMatrix.mulVec vector i

structure NegativeRationalCertificate (E : IndexedMatching Q) where
  vector : E.species → ℚ
  nonnegative : ∀ i, 0 ≤ vector i
  positive : ∃ i, 0 < vector i
  verifies : ∀ j, ∑ i, E.rationalMatrix i j * vector i ≤ 0

structure CertifiedAutocatalyticTest (Q : ReactionNetwork X R) where
  test : Finset (X × R) → Bool
  positive : ∀ edges, test edges = true →
    ∃ E : IndexedMatching Q, E.edgeFinset = edges ∧
      Nonempty (PositiveRationalCertificate E)
  negative : ∀ edges, test edges = false →
    ∀ E : IndexedMatching Q, E.edgeFinset = edges →
      NegativeRationalCertificate E

def certifiedDirectCSCoreEnum (candidates : Finset (Finset (X × R)))
    (checker : CertifiedAutocatalyticTest Q) : Finset (Finset (X × R)) :=
  candidates.filter fun edges =>
    checker.test edges && decide (∀ smaller ∈ candidates,
      smaller < edges → checker.test smaller = false)

def sourceDirectCSCoreEnum (Q : ReactionNetwork X R)
    (anchors : List (IndexedMatching Q))
    (speciesOrder : List X) (reactionOrder : List R)
    (checker : CertifiedAutocatalyticTest Q) :
    Finset (Finset (X × R)) :=
  certifiedDirectCSCoreEnum
    (allSourceCandidateEdgeFinsets Q anchors speciesOrder reactionOrder)
    checker

theorem sourceDirectCSCoreEnum_exact
    (anchors : List (IndexedMatching Q))
    (ordinary_complete : ∀ N, OrdinaryCore Q N →
      ∃ anchor ∈ anchors, anchor.underlying = N)
    (unique_anchors : ∀ anchor ∈ anchors,
      SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (speciesOrder : List X) (hspecies : ∀ x, x ∈ speciesOrder)
    (reactionOrder : List R) (hreactions : ∀ r, r ∈ reactionOrder)
    (checker : CertifiedAutocatalyticTest Q) (edges : Finset (X × R)) :
    edges ∈ sourceDirectCSCoreEnum Q anchors speciesOrder reactionOrder checker ↔
      IsCore (AutocatalyticEdgeSet Q) edges := by
  sorry

end AutocatalyticCS
