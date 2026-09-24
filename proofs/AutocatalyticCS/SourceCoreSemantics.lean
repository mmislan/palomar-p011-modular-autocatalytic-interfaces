import proofs.AutocatalyticCS.SourcePathExtraction
import proofs.AutocatalyticCS.FiniteMinimality

/-!
Source-faithful separation of the two orders used in the paper:

* ordinary cores are minimal in species/reaction support (subnetwork order);
* CS cores are minimal under restriction of one matching (edge-set order).

The distinction is essential: an ordinary core contained in a CS core may use
a different child selection on their common species.
-/

namespace AutocatalyticCS

variable {X R : Type*} [Fintype X] [Fintype R]
variable [DecidableEq X] [DecidableEq R]
variable {Q : ReactionNetwork X R}

/-- An underlying subnetwork records supports, not a chosen matching.  The
product order is componentwise inclusion. -/
abbrev Subnetwork (X R : Type*) := Finset X × Finset R

def IndexedMatching.underlying (E : IndexedMatching Q) : Subnetwork X R :=
  (E.species, E.reactions)

/-- Autocatalysis of a subnetwork allows any child selection on exactly its
supports.  In particular, passing to a smaller subnetwork may rematch a species. -/
def AutocatalyticSubnetwork (Q : ReactionNetwork X R)
    (N : Subnetwork X R) : Prop :=
  ∃ E : IndexedMatching Q,
    E.underlying = N ∧ E.toChildSelection.Autocatalytic

def OrdinaryCore (Q : ReactionNetwork X R) (N : Subnetwork X R) : Prop :=
  IsCore (AutocatalyticSubnetwork Q) N

/-- Autocatalysis carried by a matching relation, stated extensionally. -/
def AutocatalyticEdgeSet (Q : ReactionNetwork X R)
    (edges : Finset (X × R)) : Prop :=
  ∃ E : IndexedMatching Q,
    E.edgeFinset = edges ∧ E.toChildSelection.Autocatalytic

/-- Definition 3.4 minimality: only proper restrictions of the same matching
are compared. -/
def IndexedMatching.IsCSCore (E : IndexedMatching Q) : Prop :=
  E.toChildSelection.Autocatalytic ∧
    ∀ edges : Finset (X × R), edges < E.edgeFinset →
      ¬ AutocatalyticEdgeSet Q edges

omit [Fintype X] [Fintype R] [DecidableEq R] in
theorem IndexedMatching.species_card (E : IndexedMatching Q) :
    E.species.card = E.card := by
  rw [IndexedMatching.species,
    Finset.card_image_of_injective Finset.univ E.left_injective]
  simp

omit [Fintype X] [Fintype R] [DecidableEq X] in
theorem IndexedMatching.reactions_card (E : IndexedMatching Q) :
    E.reactions.card = E.card := by
  rw [IndexedMatching.reactions,
    Finset.card_image_of_injective Finset.univ E.right_injective]
  simp

omit [Fintype X] [Fintype R] in
theorem IndexedMatching.edgeFinset_card (E : IndexedMatching Q) :
    E.edgeFinset.card = E.card := by
  rw [IndexedMatching.edgeFinset,
    List.toFinset_card_of_nodup E.edgeList_nodup]
  simp [IndexedMatching.edgeList]

omit [Fintype X] [Fintype R] in
theorem IndexedMatching.card_pos_of_autocatalytic
    (E : IndexedMatching Q) (h : E.toChildSelection.Autocatalytic) :
    0 < E.card := by
  by_contra hnot
  have hzero : E.card = 0 := Nat.eq_zero_of_not_pos hnot
  rw [IndexedMatching.toChildSelection_autocatalytic_iff] at h
  rcases h with ⟨v, -, hvne, -⟩
  apply hvne
  funext i
  exfalso
  have hs : E.species = ∅ := Finset.card_eq_zero.mp (E.species_card.trans hzero)
  simpa [hs] using i.2

omit [Fintype X] [Fintype R] in
theorem IndexedMatching.isCore_edgeFinset_of_isCSCore
    (E : IndexedMatching Q) (h : E.IsCSCore) :
    IsCore (AutocatalyticEdgeSet Q) E.edgeFinset := by
  exact ⟨⟨E, rfl, h.1⟩, h.2⟩

omit [Fintype X] [Fintype R] in
theorem IndexedMatching.underlying_autocatalytic
    (E : IndexedMatching Q) (h : E.toChildSelection.Autocatalytic) :
    AutocatalyticSubnetwork Q E.underlying :=
  ⟨E, rfl, h⟩

/-- Correct ordinary-core descent: it occurs in the subnetwork-support poset,
not in the matching-edge poset. -/
theorem exists_ordinaryCore_underlying
    (E : IndexedMatching Q) (h : E.toChildSelection.Autocatalytic) :
    ∃ N ≤ E.underlying, OrdinaryCore Q N := by
  exact exists_core_le (AutocatalyticSubnetwork Q)
    (E.underlying_autocatalytic h)

omit [Fintype X] [Fintype R] in
theorem IndexedMatching.vertexContained_of_underlying_le
    {anchor target : IndexedMatching Q}
    (h : anchor.underlying ≤ target.underlying) :
    anchor.VertexContained target := by
  exact h

end AutocatalyticCS
