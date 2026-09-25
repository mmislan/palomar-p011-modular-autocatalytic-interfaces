import proofs.AutocatalyticCS.SourceSemantics
import proofs.AutocatalyticCS.PathParity

/-! The concrete reaction-network matching table as a bipartite subgraph. -/

namespace AutocatalyticCS

open _root_.SimpleGraph
open scoped symmDiff

variable {X R : Type*} [DecidableEq X] [DecidableEq R]
variable {Q : ReactionNetwork X R}

set_option backward.match.sparseCases false in
def reactantGraph (Q : ReactionNetwork X R) : _root_.SimpleGraph (X ⊕ R) where
  Adj u v := match u, v with
    | Sum.inl x, Sum.inr r => 0 < Q.reactant x r
    | Sum.inr r, Sum.inl x => 0 < Q.reactant x r
    | _, _ => False
  symm := ⟨by intro u v; cases u <;> cases v <;> simp_all⟩
  loopless := ⟨by rintro (x | r) h <;> exact h⟩

set_option backward.match.sparseCases false in
def IndexedMatching.subgraph (E : IndexedMatching Q) : (reactantGraph Q).Subgraph where
  verts := Sum.elim (fun x => x ∈ E.species) (fun r => r ∈ E.reactions)
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

theorem IndexedMatching.subgraph_isMatching (E : IndexedMatching Q) :
    E.subgraph.IsMatching := by
  intro v hv
  cases v with
  | inl x =>
      change x ∈ E.species at hv
      rw [IndexedMatching.species] at hv
      obtain ⟨i, _, hix⟩ := Finset.mem_image.mp hv
      subst x
      refine ⟨Sum.inr (E.right i), ⟨i, rfl, rfl⟩, ?_⟩
      intro w hw
      cases w with
      | inl y => exact hw.elim
      | inr r =>
          obtain ⟨j, hjx, hjr⟩ := hw
          have hji : j = i := E.left_injective (hjx.trans rfl)
          subst j
          simp_all
  | inr r =>
      change r ∈ E.reactions at hv
      rw [IndexedMatching.reactions] at hv
      obtain ⟨i, _, hir⟩ := Finset.mem_image.mp hv
      subst r
      refine ⟨Sum.inl (E.left i), ⟨i, rfl, rfl⟩, ?_⟩
      intro w hw
      cases w with
      | inl x =>
          obtain ⟨j, hjx, hjr⟩ := hw
          have hji : j = i := E.right_injective (hjr.trans rfl)
          subst j
          simp_all
      | inr s => exact hw.elim

omit [DecidableEq X] [DecidableEq R] in
theorem reactantGraph_isBipartite (Q : ReactionNetwork X R) :
    (reactantGraph Q).IsBipartiteWith {v | v.isLeft} {v | v.isRight} := by
  constructor
  · simp [Set.disjoint_left]
  · intro u v huv
    cases u with
    | inl x =>
        cases v with
        | inl y => exact huv.elim
        | inr r => simp
    | inr r =>
        cases v with
        | inl x => simp
        | inr s => exact huv.elim

def IndexedMatching.VertexContained (anchor target : IndexedMatching Q) : Prop :=
  anchor.species ⊆ target.species ∧ anchor.reactions ⊆ target.reactions

theorem IndexedMatching.vertexContained_of_edgeFinset_subset
    {anchor target : IndexedMatching Q}
    (h : anchor.edgeFinset ⊆ target.edgeFinset) :
    anchor.VertexContained target := by
  constructor
  · intro x hx
    rw [IndexedMatching.species] at hx ⊢
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    have hedge : (anchor.left i, anchor.right i) ∈ anchor.edgeFinset := by
      rw [IndexedMatching.edgeFinset, List.mem_toFinset,
        IndexedMatching.mem_edgeList_iff]
      exact ⟨i, rfl, rfl⟩
    have hedge' := h hedge
    rw [IndexedMatching.edgeFinset, List.mem_toFinset,
      IndexedMatching.mem_edgeList_iff] at hedge'
    rcases hedge' with ⟨j, hjx, hjr⟩
    exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, hjx⟩
  · intro r hr
    rw [IndexedMatching.reactions] at hr ⊢
    rcases Finset.mem_image.mp hr with ⟨i, -, rfl⟩
    have hedge : (anchor.left i, anchor.right i) ∈ anchor.edgeFinset := by
      rw [IndexedMatching.edgeFinset, List.mem_toFinset,
        IndexedMatching.mem_edgeList_iff]
      exact ⟨i, rfl, rfl⟩
    have hedge' := h hedge
    rw [IndexedMatching.edgeFinset, List.mem_toFinset,
      IndexedMatching.mem_edgeList_iff] at hedge'
    rcases hedge' with ⟨j, hjx, hjr⟩
    exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, hjr⟩

theorem IndexedMatching.subgraph_verts_mono {anchor target : IndexedMatching Q}
    (h : anchor.VertexContained target) :
    anchor.subgraph.verts ⊆ target.subgraph.verts := by
  intro v hv
  cases v with
  | inl x => exact h.1 hv
  | inr r => exact h.2 hv

theorem source_exchange_profile {anchor target : IndexedMatching Q}
    (hunique : SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (hcontains : anchor.VertexContained target) :
    SimpleGraph.IsExternalBipartitePathPack
      (anchor.subgraph.spanningCoe ∆ target.subgraph.spanningCoe)
      anchor.subgraph.spanningCoe anchor.subgraph.verts := by
  exact SimpleGraph.exchange_isExternalBipartitePathPack_of_unique_left
    hunique target.subgraph_isMatching
    (IndexedMatching.subgraph_verts_mono hcontains)
    (reactantGraph_isBipartite Q)

end AutocatalyticCS
