import Mathlib.GroupTheory.Perm.List

/-!
The contracted exchange graph of an anchor matching.  After identifying each
anchor species with its matched reaction, `edge x y` means that species `x`
may instead use the reaction currently matched to `y`.  The diagonal is the
anchor matching itself.
-/

namespace AutocatalyticCS

variable {X : Type*} [DecidableEq X]

/-- Uniqueness of the anchor perfect assignment, expressed after contraction. -/
def IsUniquePerfectAssignment (edge : X → X → Prop) : Prop :=
  ∀ σ : Equiv.Perm X, (∀ x, edge x (σ x)) → σ = 1

/-- A directed cycle in the contracted exchange graph is exactly a nontrivial
noduplicate list whose cyclic successor edges all exist. -/
def IsContractedDirectedCycle (edge : X → X → Prop) (cycle : List X) : Prop :=
  cycle.Nodup ∧ 2 ≤ cycle.length ∧
    ∀ x ∈ cycle, edge x (cycle.formPerm x)

/-- The contracted exchange graph is a DAG when it has no directed cycle. -/
def IsContractedExchangeDAG (edge : X → X → Prop) : Prop :=
  ∀ cycle, ¬ IsContractedDirectedCycle edge cycle

/-- A unique anchor assignment globally forbids cycles in its contracted
exchange graph.  A cycle permutation uses its directed exchange edges on the
cycle and the diagonal anchor edges everywhere else, giving a second perfect
assignment. -/
theorem contractedExchange_isDAG_of_uniqueMatching
    (edge : X → X → Prop)
    (diagonal : ∀ x, edge x x)
    (unique : IsUniquePerfectAssignment edge) :
    IsContractedExchangeDAG edge := by
  intro cycle hcycle
  rcases hcycle with ⟨hnodup, hlength, hedges⟩
  have hall : ∀ x, edge x (cycle.formPerm x) := by
    intro x
    by_cases hx : x ∈ cycle
    · exact hedges x hx
    · rw [cycle.formPerm_apply_of_notMem hx]
      exact diagonal x
  have hidentity : cycle.formPerm = 1 := unique cycle.formPerm hall
  obtain ⟨x, y, tail, rfl⟩ : ∃ x y tail, cycle = x :: y :: tail := by
    match cycle with
    | x :: y :: tail => exact ⟨x, y, tail, rfl⟩
    | [] => simp at hlength
    | [_] => simp at hlength
  have hxmem : x ∈ x :: y :: tail := by simp
  have hmoved : (x :: y :: tail).formPerm x ≠ x :=
    ((x :: y :: tail).formPerm_apply_mem_ne_self_iff hnodup x hxmem).2 (by simp)
  apply hmoved
  rw [hidentity]
  rfl

end AutocatalyticCS
