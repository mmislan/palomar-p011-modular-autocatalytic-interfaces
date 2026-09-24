import Mathlib
import proofs.MAFComposition.Composition

/-!
Exact one-reaction edit calculus: adding a reaction intersects the old strict
price cone with one open linear half-space and cannot decrease an attained MAF.
-/

namespace MAFComposition

open Set

variable {ι κ : Type} [Fintype ι] [Fintype κ]

def Network.singleReaction (a b : ι → ℝ) : Network ι Unit where
  input := singletonColumn a
  output := singletonColumn b

def Network.addReaction (N : Network ι κ) (a b : ι → ℝ) :
    Network ι (Sum κ Unit) :=
  N.parallel (Network.singleReaction a b)

def reactionHalfspace (a b : ι → ℝ) (q : ℝ) : Set (ι → ℝ) :=
  {p | weightedColumn p (singletonColumn b) () <
    q * weightedColumn p (singletonColumn a) ()}

omit [Fintype κ] in
theorem priceCone_addReaction (N : Network ι κ) (a b : ι → ℝ) (q : ℝ) :
    (N.addReaction a b).priceCone q =
      N.priceCone q ∩ reactionHalfspace a b q := by
  ext p
  exact strictObstruction_addReaction_iff N.input N.output a b q p

theorem feasibleAt_addReaction_of_base (N : Network ι κ) (a b : ι → ℝ)
    (q : ℝ) (h : N.FeasibleAt q) : (N.addReaction a b).FeasibleAt q := by
  exact feasibleAt_parallel_of_left N (Network.singleReaction a b) q h

theorem maf_le_addReaction_maf (N : Network ι κ) (a b : ι → ℝ)
    {α β : ℝ} (hα : N.IsMAF α) (hβ : (N.addReaction a b).IsMAF β) : α ≤ β := by
  exact hβ.2 α (feasibleAt_addReaction_of_base N a b α hα.1)

def VectorNonnegative (v : ι → ℝ) : Prop := ∀ i, 0 ≤ v i

omit [Fintype ι] [Fintype κ] in
theorem inputNonnegative_addReaction (N : Network ι κ)
    (hN : N.InputNonnegative) (a b : ι → ℝ) (ha : VectorNonnegative a) :
    (N.addReaction a b).InputNonnegative := by
  intro i r
  cases r with
  | inl r => exact hN i r
  | inr r => simpa [Network.addReaction, Network.parallel,
      Network.singleReaction, singletonColumn] using ha i

theorem addReaction_isMAF_same_iff_pricesAbove
    (N : Network ι κ) (hN : N.InputNonnegative)
    (a b : ι → ℝ) (ha0 : VectorNonnegative a) {α : ℝ} (hα : N.IsMAF α) :
    (N.addReaction a b).IsMAF α ↔
      ∀ q, α < q → ∃ p, p ∈ N.priceCone q ∩ reactionHalfspace a b q := by
  constructor
  · intro hadd q hq
    have hp := (hadd.lt_iff_strictPriceAt
      (inputNonnegative_addReaction N hN a b ha0) q).mp hq
    obtain ⟨p, hp⟩ := (strictPriceAt_iff_exists_obstruction
      (N.addReaction a b) q).mp hp
    exact ⟨p, (Set.ext_iff.mp (priceCone_addReaction N a b q) p).mp hp⟩
  · intro hprices
    constructor
    · exact feasibleAt_addReaction_of_base N a b α hα.1
    · intro q hq
      by_contra hnot
      have hlt : α < q := lt_of_not_ge hnot
      obtain ⟨p, hp⟩ := hprices q hlt
      have hpadd : p ∈ (N.addReaction a b).priceCone q :=
        (Set.ext_iff.mp (priceCone_addReaction N a b q) p).mpr hp
      have hstrict : (N.addReaction a b).StrictPriceAt q :=
        (strictPriceAt_iff_exists_obstruction (N.addReaction a b) q).mpr ⟨p, hpadd⟩
      exact (feasibleAt_iff_not_strictPriceAt (N.addReaction a b) q).mp hq hstrict

theorem addReaction_strictIncrease_iff_no_pricesAbove
    (N : Network ι κ) (hN : N.InputNonnegative)
    (a b : ι → ℝ) (ha0 : VectorNonnegative a)
    {α β : ℝ} (hα : N.IsMAF α) (hβ : (N.addReaction a b).IsMAF β) :
    α < β ↔
      ¬ ∀ q, α < q → ∃ p, p ∈ N.priceCone q ∩ reactionHalfspace a b q := by
  have hle : α ≤ β := maf_le_addReaction_maf N a b hα hβ
  rw [← addReaction_isMAF_same_iff_pricesAbove N hN a b ha0 hα]
  constructor
  · intro hlt heq
    have := hβ.unique heq
    linarith
  · intro hne
    exact lt_of_le_of_ne hle fun heq => hne (heq ▸ hβ)

end MAFComposition
