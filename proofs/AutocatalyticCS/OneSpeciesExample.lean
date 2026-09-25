import proofs.AutocatalyticCS.SourceDirectEnumeration

/-!
# A nonempty instance of certified direct core enumeration

Original work: Michael Mislan, 2026. Licensed under Apache-2.0.

The one-species, one-reaction network `A → 2A` satisfies every hypothesis of
`sourceDirectCSCoreEnum_exact`: the supplied anchor list is complete for the
ordinary cores, its matching is the unique matching on its vertices, the
species and reaction orders are exhaustive, and a certified checker exists.
For every certified checker, the enumerator returns exactly the one-edge
child-selection core.
-/

namespace AutocatalyticCS
namespace OneSpeciesExample

/-- The network `A → 2A`: one species and one reaction that consumes one copy
of the species and produces two. -/
def network : ReactionNetwork Unit Unit where
  reactant _ _ := 1
  product _ _ := 2

/-- The anchor matching assigning the species to the reaction. -/
def anchor : IndexedMatching network where
  card := 1
  left _ := ()
  right _ := ()
  left_injective := fun i j _ => Subsingleton.elim i j
  right_injective := fun i j _ => Subsingleton.elim i j
  reactant_edge _ := Nat.one_pos

theorem finset_eq_singleton_of_nonempty {α : Type*} [Subsingleton α] {s : Finset α}
    (h : s.Nonempty) (a : α) : s = {a} := by
  obtain ⟨b, hb⟩ := h
  rw [Subsingleton.elim b a] at hb
  exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hb, fun c _ => Subsingleton.elim c a⟩

theorem anchor_species : anchor.species = {()} :=
  finset_eq_singleton_of_nonempty
    ⟨anchor.left ⟨0, Nat.one_pos⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ ()

theorem anchor_reactions : anchor.reactions = {()} :=
  finset_eq_singleton_of_nonempty
    ⟨anchor.right ⟨0, Nat.one_pos⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ ()

theorem anchor_edgeFinset : anchor.edgeFinset = {((), ())} :=
  finset_eq_singleton_of_nonempty
    ⟨((), ()), List.mem_toFinset.mpr
      ((anchor.mem_edgeList_iff () ()).mpr ⟨⟨0, Nat.one_pos⟩, rfl, rfl⟩)⟩ ((), ())

theorem anchor_autocatalytic : anchor.toChildSelection.Autocatalytic := by
  rw [IndexedMatching.toChildSelection_autocatalytic_iff]
  have hmem : () ∈ anchor.species := by simp [anchor_species]
  refine ⟨fun _ => 1, fun _ => zero_le_one, fun h => ?_, fun i => ?_⟩
  · exact one_ne_zero (congrFun h ⟨(), hmem⟩)
  · simp only [Matrix.mulVec, dotProduct, mul_one]
    refine Finset.sum_pos (fun j _ => ?_) ⟨⟨(), hmem⟩, Finset.mem_univ _⟩
    simp [ReactionNetwork.net, network]

/-- The child-selection cores of `A → 2A`: exactly the one-edge set. -/
theorem isCore_iff (edges : Finset (Unit × Unit)) :
    IsCore (AutocatalyticEdgeSet network) edges ↔ edges = {((), ())} := by
  constructor
  · intro h
    rcases edges.eq_empty_or_nonempty with rfl | hne
    · exact absurd h.1 not_autocatalyticEdgeSet_empty
    · exact finset_eq_singleton_of_nonempty hne ((), ())
  · rintro rfl
    refine ⟨⟨anchor, anchor_edgeFinset, anchor_autocatalytic⟩, fun b hb hgood => ?_⟩
    rw [Finset.ssubset_singleton_iff] at hb
    subst hb
    exact not_autocatalyticEdgeSet_empty hgood

/-- The single anchor is complete for the ordinary cores. -/
theorem ordinary_complete :
    ∀ N, OrdinaryCore network N → ∃ a ∈ [anchor], a.underlying = N := by
  intro N hN
  obtain ⟨E, hE, hauto⟩ := hN.1
  refine ⟨anchor, by simp, ?_⟩
  rw [← hE]
  have hs := E.species_nonempty_of_autocatalytic hauto
  have hr : E.reactions.Nonempty := by
    rw [← Finset.card_pos, E.reactions_card, ← E.species_card, Finset.card_pos]
    exact hs
  simp only [IndexedMatching.underlying]
  rw [finset_eq_singleton_of_nonempty hs (), finset_eq_singleton_of_nonempty hr (),
    anchor_species, anchor_reactions]

/-- The anchor's matching is the unique matching on its vertex set. -/
theorem anchor_isUniqueMatching :
    SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph := by
  refine ⟨anchor.subgraph_isMatching, fun M hM hverts => ?_⟩
  have hinl : (Sum.inl () : Unit ⊕ Unit) ∈ M.verts := by
    rw [hverts]
    change () ∈ anchor.species
    simp [anchor_species]
  obtain ⟨w, hw, -⟩ := hM hinl
  have hedge : M.Adj (Sum.inl ()) (Sum.inr ()) := by
    rcases w with ⟨⟩ | ⟨⟩
    · exact False.elim (M.adj_sub hw)
    · exact hw
  apply _root_.SimpleGraph.Subgraph.ext hverts
  funext u v
  apply propext
  rcases u with ⟨⟩ | ⟨⟩ <;> rcases v with ⟨⟩ | ⟨⟩
  · exact ⟨fun h => False.elim (M.adj_sub h), fun h => False.elim h⟩
  · exact ⟨fun _ => ⟨⟨0, Nat.one_pos⟩, rfl, rfl⟩, fun _ => hedge⟩
  · exact ⟨fun _ => ⟨⟨0, Nat.one_pos⟩, rfl, rfl⟩, fun _ => M.adj_symm hedge⟩
  · exact ⟨fun h => False.elim (M.adj_sub h), fun h => False.elim h⟩

/-- **A nonempty applicable instance.** For `A → 2A`, with the single anchor
and the (necessarily exhaustive) singleton orders, every hypothesis of
`sourceDirectCSCoreEnum_exact` holds, a certified checker exists, the one-edge
set is a child-selection core, and every certified checker makes the enumerator
return exactly that core. -/
theorem sourceDirectCSCoreEnum_example :
    (∀ x : Unit, x ∈ [()]) ∧ (∀ r : Unit, r ∈ [()]) ∧
    (∀ N, OrdinaryCore network N → ∃ a ∈ [anchor], a.underlying = N) ∧
    (∀ a ∈ [anchor], SimpleGraph.Subgraph.IsUniqueMatching a.subgraph) ∧
    Nonempty (CertifiedAutocatalyticTest network) ∧
    IsCore (AutocatalyticEdgeSet network) {((), ())} ∧
    ∀ checker : CertifiedAutocatalyticTest network,
      sourceDirectCSCoreEnum network [anchor] [()] [()] checker = {{((), ())}} := by
  have hunique : ∀ a ∈ [anchor], SimpleGraph.Subgraph.IsUniqueMatching a.subgraph := by
    intro a ha
    rw [List.mem_singleton] at ha
    subst ha
    exact anchor_isUniqueMatching
  refine ⟨fun _ => by simp, fun _ => by simp, ordinary_complete, hunique,
    certifiedAutocatalyticTest_nonempty network, (isCore_iff _).2 rfl,
    fun checker => ?_⟩
  ext edges
  rw [sourceDirectCSCoreEnum_exact [anchor] ordinary_complete hunique [()]
    (fun _ => by simp) [()] (fun _ => by simp) checker edges, isCore_iff,
    Finset.mem_singleton]

end OneSpeciesExample
end AutocatalyticCS
