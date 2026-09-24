import proofs.AutocatalyticCS.SourceCoreSemantics

/-!
Completeness of the direct source-derived candidate family after ordinary-core
descent in the support poset.  No inclusion between the anchor and target
matching relations is assumed.
-/

namespace AutocatalyticCS

variable {X R : Type*} [Fintype X] [Fintype R]
variable [DecidableEq X] [DecidableEq R]
variable {Q : ReactionNetwork X R}

def allSourceCandidateEdgeFinsets (Q : ReactionNetwork X R)
    (anchors : List (IndexedMatching Q))
    (speciesOrder : List X) (reactionOrder : List R) :
    Finset (Finset (X × R)) :=
  (anchors.flatMap fun anchor =>
    sourceCandidateEdgeFinsets Q anchor speciesOrder reactionOrder).toFinset

theorem autocatalyticEdgeSet_mem_allSourceCandidateEdgeFinsets
    (anchors : List (IndexedMatching Q))
    (ordinary_complete : ∀ N, OrdinaryCore Q N →
      ∃ anchor ∈ anchors, anchor.underlying = N)
    (unique_anchors : ∀ anchor ∈ anchors,
      SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (speciesOrder : List X) (hspecies : ∀ x, x ∈ speciesOrder)
    (reactionOrder : List R) (hreactions : ∀ r, r ∈ reactionOrder)
    {edges : Finset (X × R)} (hauto : AutocatalyticEdgeSet Q edges) :
    edges ∈ allSourceCandidateEdgeFinsets Q anchors
      speciesOrder reactionOrder := by
  rcases hauto with ⟨target, rfl, htarget⟩
  obtain ⟨N, hNle, hNcore⟩ :=
    exists_ordinaryCore_underlying target htarget
  obtain ⟨anchor, hanchor, hanchorN⟩ := ordinary_complete N hNcore
  have hcontains : anchor.VertexContained target :=
    IndexedMatching.vertexContained_of_underlying_le (hanchorN.le.trans hNle)
  have hemitted := target_edgeFinset_mem_sourceCandidateEdgeFinsets
    (unique_anchors anchor hanchor) hcontains
    speciesOrder hspecies reactionOrder hreactions
  rw [allSourceCandidateEdgeFinsets, List.mem_toFinset, List.mem_flatMap]
  exact ⟨anchor, hanchor, hemitted⟩

end AutocatalyticCS
