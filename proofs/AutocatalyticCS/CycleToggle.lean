import proofs.AutocatalyticCS.ExchangeProfile

open scoped symmDiff

namespace AutocatalyticCS
namespace SimpleGraph

open _root_.SimpleGraph

variable {V : Type*} {A : _root_.SimpleGraph V}

noncomputable def toggleSubgraph (M : A.Subgraph) (C : _root_.SimpleGraph V)
    (hC : C ≤ A) (hverts : C.support ⊆ M.verts) : A.Subgraph where
  verts := M.verts
  Adj := (M.spanningCoe ∆ C).Adj
  adj_sub := by
    intro v w h
    simp only [symmDiff_def, _root_.SimpleGraph.sup_adj,
      _root_.SimpleGraph.sdiff_adj, Subgraph.spanningCoe_adj] at h
    rcases h with h | h
    · exact M.adj_sub h.1
    · exact hC h.1
  edge_vert := by
    intro v w h
    simp only [symmDiff_def, _root_.SimpleGraph.sup_adj,
      _root_.SimpleGraph.sdiff_adj, Subgraph.spanningCoe_adj] at h
    rcases h with h | h
    · exact M.edge_vert h.1
    · exact hverts h.1.mem_support_left
  symm := (M.spanningCoe ∆ C).symm

theorem toggleSubgraph_isMatching {M : A.Subgraph} (hM : M.IsMatching)
    {C : _root_.SimpleGraph V} (hC : C ≤ A) (hverts : C.support ⊆ M.verts)
    (halt : C.IsAlternating M.spanningCoe) (hcycles : C.IsCycles) :
    (toggleSubgraph M C hC hverts).IsMatching := by
  intro v hv
  change ∃! w, (M.spanningCoe ∆ C).Adj v w
  obtain ⟨w, hw⟩ := hM hv
  by_cases h : C.Adj v w
  · obtain ⟨w', hw'⟩ := hcycles.other_adj_of_adj h
    have hmadj : M.Adj v w ↔ ¬M.Adj v w' := by
      simpa using halt hw'.1 h hw'.2
    use w'
    simp only [symmDiff_def, _root_.SimpleGraph.sup_adj,
      _root_.SimpleGraph.sdiff_adj, Subgraph.spanningCoe_adj,
      hmadj.mp hw.1, hw'.2, not_true_eq_false, and_self,
      not_false_eq_true, or_true, true_and]
    rintro y (hl | hr)
    · exfalso
      exact hl.2 (by simpa [hw.2 _ hl.1] using h)
    · obtain ⟨w'', hw''⟩ := hcycles.other_adj_of_adj hr.1
      by_contra! hc
      simp_all [show M.Adj v y ↔ ¬M.Adj v w' from by
        simpa using halt hc hr.1 hw'.2]
  · use w
    simp only [symmDiff_def, _root_.SimpleGraph.sup_adj,
      _root_.SimpleGraph.sdiff_adj, Subgraph.spanningCoe_adj,
      hw.1, h, not_false_eq_true, and_self, not_true_eq_false,
      or_false, true_and]
    rintro y (hl | hr)
    · exact hw.2 _ hl.1
    · have ⟨w', hw'⟩ := hcycles.other_adj_of_adj hr.1
      simp_all [show M.Adj v y ↔ ¬M.Adj v w' from by
        simpa using halt hw'.1 hr.1 hw'.2]

theorem cycles_support_subset_left {M M' : A.Subgraph} (hM' : M'.IsMatching)
    {C : _root_.SimpleGraph V} (hcycles : C.IsCycles)
    (hsub : C ≤ M.spanningCoe ∆ M'.spanningCoe) : C.support ⊆ M.verts := by
  intro v hv
  by_contra hnot
  obtain ⟨w, hw⟩ := (_root_.SimpleGraph.mem_support (G := C)).mp hv
  obtain ⟨w', hne, hw'⟩ := hcycles.other_adj_of_adj hw
  have hnotM : ∀ y, ¬M.Adj v y := fun y h => hnot (M.edge_vert h)
  have hm'w : M'.Adj v w := by
    have := hsub hw
    simpa [symmDiff_def, hnotM] using this
  have hm'w' : M'.Adj v w' := by
    have := hsub hw'
    simpa [symmDiff_def, hnotM] using this
  exact hne (Subgraph.IsMatching.eq_of_adj_left hM' hm'w hm'w')

def Subgraph.IsUniqueMatching (M : A.Subgraph) : Prop :=
  M.IsMatching ∧ ∀ N : A.Subgraph, N.IsMatching → N.verts = M.verts → N = M

theorem symmDiff_isAcyclic_of_unique_left {M M' : A.Subgraph}
    (hunique : Subgraph.IsUniqueMatching M) (hM' : M'.IsMatching) :
    (M.spanningCoe ∆ M'.spanningCoe).IsAcyclic := by
  intro v c hcycle
  let C : _root_.SimpleGraph V := c.toSubgraph.spanningCoe
  have hcycles : C.IsCycles := hcycle.isCycles_spanningCoe_toSubgraph
  have hsub : C ≤ M.spanningCoe ∆ M'.spanningCoe := by
    intro x y hxy
    exact c.toSubgraph.adj_sub hxy
  have hverts : C.support ⊆ M.verts :=
    cycles_support_subset_left hM' hcycles hsub
  have hdiffA : M.spanningCoe ∆ M'.spanningCoe ≤ A := by
    intro x y hxy
    simp only [symmDiff_def, _root_.SimpleGraph.sup_adj,
      _root_.SimpleGraph.sdiff_adj, Subgraph.spanningCoe_adj] at hxy
    rcases hxy with hxy | hxy
    · exact M.adj_sub hxy.1
    · exact M'.adj_sub hxy.1
  have hCA : C ≤ A := hsub.trans hdiffA
  have halt : C.IsAlternating M.spanningCoe :=
    (Subgraph.IsMatching.isAlternating_symmDiff_left hunique.1 hM').mono hsub
  let N : A.Subgraph := toggleSubgraph M C hCA hverts
  have hNmatch : N.IsMatching := toggleSubgraph_isMatching hunique.1 hCA hverts halt hcycles
  have hNverts : N.verts = M.verts := rfl
  have hNM : N = M := hunique.2 N hNmatch hNverts
  have hc : C.Adj v c.snd := by
    exact c.toSubgraph_adj_snd hcycle.not_nil
  have hadjEq : N.Adj v c.snd ↔ M.Adj v c.snd := by rw [hNM]
  by_cases hm : M.Adj v c.snd
  · have hnnot : ¬N.Adj v c.snd := by
      change ¬(M.spanningCoe ∆ C).Adj v c.snd
      simp only [symmDiff_def, _root_.SimpleGraph.sup_adj,
        _root_.SimpleGraph.sdiff_adj, Subgraph.spanningCoe_adj, not_or,
        not_and, not_not]
      exact ⟨fun _ => hc, fun _ => hm⟩
    exact hnnot (hadjEq.mpr hm)
  · have hn : N.Adj v c.snd := by
      change (M.spanningCoe ∆ C).Adj v c.snd
      simp only [symmDiff_def, _root_.SimpleGraph.sup_adj,
        _root_.SimpleGraph.sdiff_adj, Subgraph.spanningCoe_adj]
      exact Or.inr ⟨hc, hm⟩
    exact hm (hadjEq.mp hn)

theorem exchange_isPathPack_of_unique_left {M M' : A.Subgraph}
    (hunique : Subgraph.IsUniqueMatching M) (hM' : M'.IsMatching) :
    IsAlternatingPathPack (M.spanningCoe ∆ M'.spanningCoe) M.spanningCoe :=
  exchange_isPathPack hunique.1 hM'
    (symmDiff_isAcyclic_of_unique_left hunique hM')

/-- The complete graph-theoretic exchange profile used by the generator:
the exchange is an alternating path pack and its endpoints are exactly the
vertices external to the unique inner matching. -/
theorem exchange_isExternalEndpointPathPack_of_unique_left {M M' : A.Subgraph}
    (hunique : Subgraph.IsUniqueMatching M) (hM' : M'.IsMatching)
    (hverts : M.verts ⊆ M'.verts) :
    IsAlternatingPathPack (M.spanningCoe ∆ M'.spanningCoe) M.spanningCoe ∧
      HasExternalEndpoints (M.spanningCoe ∆ M'.spanningCoe) M.verts :=
  ⟨exchange_isPathPack_of_unique_left hunique hM',
    Subgraph.IsMatching.hasExternalEndpoints_symmDiff
      hunique.1 hM' hverts⟩

end SimpleGraph
end AutocatalyticCS
