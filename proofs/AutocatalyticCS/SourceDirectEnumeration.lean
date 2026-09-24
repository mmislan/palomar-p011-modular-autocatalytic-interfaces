import proofs.AutocatalyticCS.CertifiedDirectEnumeration

/-!
Paper-level endpoint: direct path-pack generation from the promised complete
ordinary-core anchors, exact rational autocatalyticity certificates, and
minimality among smaller generated autocatalytic matchings.
-/

namespace AutocatalyticCS

variable {X R : Type*} [Fintype X] [Fintype R]
variable [DecidableEq X] [DecidableEq R]
variable {Q : ReactionNetwork X R}

def sourceDirectCSCoreEnum (Q : ReactionNetwork X R)
    (anchors : List (IndexedMatching Q))
    (speciesOrder : List X) (reactionOrder : List R)
    (checker : CertifiedAutocatalyticTest Q) :
    Finset (Finset (X × R)) :=
  certifiedDirectCSCoreEnum
    (allSourceCandidateEdgeFinsets Q anchors speciesOrder reactionOrder)
    checker

/-- Exact source-specific direct extraction.  The terminal statement contains
neither an abstract ordinary predicate nor a CS-core predicate/test.  Its only
semantic input is completeness of the supplied ordinary-core anchors; the
algebraic input consists of independently checked rational primal/dual
certificates. -/
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
  apply mem_certifiedDirectCSCoreEnum_iff
  intro candidate hauto
  exact autocatalyticEdgeSet_mem_allSourceCandidateEdgeFinsets
    anchors ordinary_complete unique_anchors
    speciesOrder hspecies reactionOrder hreactions hauto

end AutocatalyticCS
