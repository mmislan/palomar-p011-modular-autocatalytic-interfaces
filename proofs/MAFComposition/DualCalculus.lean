import Mathlib

/-!
Exact set-level composition identities for strict MAF price obstructions.

The missing global theorem is the finite Gordan alternative connecting these
strict certificates to infeasibility.  The identities here do not assume that
duality theorem and are therefore definitionally trustworthy.
-/

namespace MAFComposition

open scoped BigOperators

variable {ι κ ρ : Type*} [Fintype ι]

def weightedColumn (p : ι → ℝ) (M : ι → κ → ℝ) (r : κ) : ℝ :=
  ∑ i, p i * M i r

def StrictObstruction (A B : ι → κ → ℝ) (q : ℝ) (p : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∀ r, weightedColumn p B r < q * weightedColumn p A r

def WeakProductivityObstruction (S : ι → κ → ℝ) (p : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∃ i, p i ≠ 0) ∧ ∀ r, weightedColumn p S r ≤ 0

def parallelColumns (M₁ : ι → κ → ℝ) (M₂ : ι → ρ → ℝ) :
    ι → Sum κ ρ → ℝ :=
  fun i r => Sum.elim (M₁ i) (M₂ i) r

theorem strictObstruction_parallel_iff
    (A₁ B₁ : ι → κ → ℝ) (A₂ B₂ : ι → ρ → ℝ) (q : ℝ) (p : ι → ℝ) :
    StrictObstruction (parallelColumns A₁ A₂) (parallelColumns B₁ B₂) q p ↔
      StrictObstruction A₁ B₁ q p ∧ StrictObstruction A₂ B₂ q p := by
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨⟨hp, fun r => ?_⟩, ⟨hp, fun r => ?_⟩⟩
    · simpa [weightedColumn, parallelColumns] using h (Sum.inl r)
    · simpa [weightedColumn, parallelColumns] using h (Sum.inr r)
  · rintro ⟨⟨hp, h₁⟩, ⟨_, h₂⟩⟩
    refine ⟨hp, fun r => ?_⟩
    cases r with
    | inl r => simpa [weightedColumn, parallelColumns] using h₁ r
    | inr r => simpa [weightedColumn, parallelColumns] using h₂ r

theorem weakProductivityObstruction_parallel_iff
    (S₁ : ι → κ → ℝ) (S₂ : ι → ρ → ℝ) (p : ι → ℝ) :
    WeakProductivityObstruction (parallelColumns S₁ S₂) p ↔
      WeakProductivityObstruction S₁ p ∧ WeakProductivityObstruction S₂ p := by
  constructor
  · rintro ⟨hp, hn, h⟩
    refine ⟨⟨hp, hn, fun r => ?_⟩, ⟨hp, hn, fun r => ?_⟩⟩
    · simpa [weightedColumn, parallelColumns] using h (Sum.inl r)
    · simpa [weightedColumn, parallelColumns] using h (Sum.inr r)
  · rintro ⟨⟨hp, hn, h₁⟩, ⟨_, _, h₂⟩⟩
    refine ⟨hp, hn, fun r => ?_⟩
    cases r with
    | inl r => simpa [weightedColumn, parallelColumns] using h₁ r
    | inr r => simpa [weightedColumn, parallelColumns] using h₂ r

def singletonColumn (v : ι → ℝ) : ι → Unit → ℝ := fun i _ => v i

theorem strictObstruction_addReaction_iff
    (A B : ι → κ → ℝ) (a b : ι → ℝ) (q : ℝ) (p : ι → ℝ) :
    StrictObstruction (parallelColumns A (singletonColumn a))
        (parallelColumns B (singletonColumn b)) q p ↔
      StrictObstruction A B q p ∧
        weightedColumn p (singletonColumn b) () <
          q * weightedColumn p (singletonColumn a) () := by
  rw [strictObstruction_parallel_iff]
  constructor
  · rintro ⟨hbase, hp, hunit⟩
    exact ⟨hbase, hunit ()⟩
  · rintro ⟨hbase, hineq⟩
    exact ⟨hbase, hbase.1, fun _ => hineq⟩

theorem weakObstruction_addReaction_iff
    (S : ι → κ → ℝ) (d : ι → ℝ) (p : ι → ℝ) :
    WeakProductivityObstruction (parallelColumns S (singletonColumn d)) p ↔
      WeakProductivityObstruction S p ∧
        weightedColumn p (singletonColumn d) () ≤ 0 := by
  rw [weakProductivityObstruction_parallel_iff]
  constructor
  · rintro ⟨hbase, hp, hn, hunit⟩
    exact ⟨hbase, hunit ()⟩
  · rintro ⟨hbase, hineq⟩
    exact ⟨hbase, hbase.1, hbase.2.1, fun _ => hineq⟩

end MAFComposition
