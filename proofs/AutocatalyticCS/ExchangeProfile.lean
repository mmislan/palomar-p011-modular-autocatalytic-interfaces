import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
The graph-theoretic kernel of matching exchange.  A finite acyclic graph whose
edges alternate between two matchings is precisely the local object needed by
the path-pack generator; isolated vertices are irrelevant.
-/

open scoped symmDiff

namespace AutocatalyticCS
namespace SimpleGraph

open _root_.SimpleGraph

variable {V : Type*} {G G' : _root_.SimpleGraph V}
variable {M : G.Subgraph} {M' : G'.Subgraph}

def IsAlternatingPathPack (P reference : _root_.SimpleGraph V) : Prop :=
  P.IsAcyclic ∧ P.IsAlternating reference

/-- The endpoint condition needed by the anchored generator: among vertices
that occur in the exchange graph, degree one is equivalent to being external
to the inner matching. -/
def HasExternalEndpoints (P : _root_.SimpleGraph V) (inner : Set V) : Prop :=
  ∀ ⦃v⦄, v ∈ P.support → ((∃! w, P.Adj v w) ↔ v ∉ inner)

theorem IsAlternating.ncard_neighborSet_le_two [Finite V]
    {P reference : _root_.SimpleGraph V}
    (halt : P.IsAlternating reference) (v : V) :
    (P.neighborSet v).ncard ≤ 2 := by
  classical
  by_contra hle
  have hlt : 2 < (P.neighborSet v).ncard := Nat.lt_of_not_ge hle
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite (P.neighborSet v))).mp hlt
  simp only [_root_.SimpleGraph.mem_neighborSet] at ha hb hc
  have eab := halt hab ha hb
  have eac := halt hac ha hc
  have ebc := halt hbc hb hc
  tauto

theorem Subgraph.IsMatching.isAlternating_symmDiff_left
    (hM : M.IsMatching) (hM' : M'.IsMatching) :
    (M.spanningCoe ∆ M'.spanningCoe).IsAlternating M.spanningCoe := by
  intro v w w' hww' hvw hvw'
  simp only [symmDiff_def, _root_.SimpleGraph.sup_adj,
    _root_.SimpleGraph.sdiff_adj, Subgraph.spanningCoe_adj] at hvw hvw' ⊢
  rcases hvw with hw | hw <;> rcases hvw' with hw' | hw'
  · exact (hww' (hM.eq_of_adj_left hw.1 hw'.1)).elim
  · constructor
    · intro _ hm'
      exact hww' (hM.eq_of_adj_left hw.1 hm')
    · intro _
      exact hw.1
  · constructor
    · intro hm
      exact (hw.2 hm).elim
    · intro hn
      exact (hn hw'.1).elim
  · exact (hww' (hM'.eq_of_adj_left hw.1 hw'.1)).elim

theorem Subgraph.IsMatching.isAlternating_symmDiff_right
    (hM : M.IsMatching) (hM' : M'.IsMatching) :
    (M.spanningCoe ∆ M'.spanningCoe).IsAlternating M'.spanningCoe := by
  simpa [symmDiff_comm] using
    isAlternating_symmDiff_left (M := M') (M' := M) hM' hM

/-- A vertex unmatched by the inner matching is an endpoint whenever it occurs
in the exchange graph.  This is the exact local statement behind “all path
endpoints are external”. -/
theorem Subgraph.IsMatching.existsUnique_symmDiff_adj_of_not_mem_verts
    (hM' : M'.IsMatching) {v : V} (hv : v ∉ M.verts)
    (hsupport : v ∈ (M.spanningCoe ∆ M'.spanningCoe).support) :
    ∃! w, (M.spanningCoe ∆ M'.spanningCoe).Adj v w := by
  have hnotM : ∀ w, ¬M.Adj v w := fun w h => hv (M.edge_vert h)
  obtain ⟨w, hw⟩ := (_root_.SimpleGraph.mem_support
    (G := M.spanningCoe ∆ M'.spanningCoe)).mp hsupport
  refine ⟨w, hw, ?_⟩
  intro y hy
  have hw' : M'.Adj v w := by
    simpa [symmDiff_def, hnotM] using hw
  have hy' : M'.Adj v y := by
    simpa [symmDiff_def, hnotM] using hy
  exact (Subgraph.IsMatching.eq_of_adj_left hM' (u := v) (v := w) (w := y) hw' hy').symm

/-- A vertex matched by both matchings has either zero exchange edges (the
matchings agree) or two distinct exchange edges. -/
theorem Subgraph.IsMatching.exists_two_symmDiff_adj_of_mem_both
    (hM : M.IsMatching) (hM' : M'.IsMatching) {v : V}
    (hvM : v ∈ M.verts) (hvM' : v ∈ M'.verts)
    (hsupport : v ∈ (M.spanningCoe ∆ M'.spanningCoe).support) :
    ∃ w w', w ≠ w' ∧
      (M.spanningCoe ∆ M'.spanningCoe).Adj v w ∧
      (M.spanningCoe ∆ M'.spanningCoe).Adj v w' := by
  obtain ⟨w, hw, hwuniq⟩ := hM hvM
  obtain ⟨w', hw', hw'uniq⟩ := hM' hvM'
  have hne : w ≠ w' := by
    intro heq
    subst w'
    obtain ⟨y, hy⟩ := (_root_.SimpleGraph.mem_support
      (G := M.spanningCoe ∆ M'.spanningCoe)).mp hsupport
    simp only [symmDiff_def, _root_.SimpleGraph.sup_adj,
      _root_.SimpleGraph.sdiff_adj, Subgraph.spanningCoe_adj] at hy
    rcases hy with hy | hy
    · have hyw : y = w := hwuniq _ hy.1
      subst y
      exact hy.2 hw'
    · have hyw : y = w := hw'uniq _ hy.1
      subst y
      exact hy.2 hw
  refine ⟨w, w', hne, ?_, ?_⟩
  · simp only [symmDiff_def, _root_.SimpleGraph.sup_adj,
      _root_.SimpleGraph.sdiff_adj, Subgraph.spanningCoe_adj]
    exact Or.inl ⟨hw, fun h => hne (hw'uniq _ h)⟩
  · simp only [symmDiff_def, _root_.SimpleGraph.sup_adj,
      _root_.SimpleGraph.sdiff_adj, Subgraph.spanningCoe_adj]
    exact Or.inr ⟨hw', fun h => hne (hwuniq _ h).symm⟩

theorem Subgraph.IsMatching.hasExternalEndpoints_symmDiff
    (hM : M.IsMatching) (hM' : M'.IsMatching)
    (hverts : M.verts ⊆ M'.verts) :
    HasExternalEndpoints (M.spanningCoe ∆ M'.spanningCoe) M.verts := by
  intro v hsupport
  constructor
  · intro hunique hvM
    obtain ⟨w, w', hne, hw, hw'⟩ :=
      Subgraph.IsMatching.exists_two_symmDiff_adj_of_mem_both
        hM hM' hvM (hverts hvM) hsupport
    exact hne (hunique.unique hw hw')
  · intro hvM
    exact Subgraph.IsMatching.existsUnique_symmDiff_adj_of_not_mem_verts
      hM' hvM hsupport

theorem exchange_isPathPack (hM : M.IsMatching) (hM' : M'.IsMatching)
    (hacyclic : (M.spanningCoe ∆ M'.spanningCoe).IsAcyclic) :
    IsAlternatingPathPack (M.spanningCoe ∆ M'.spanningCoe) M.spanningCoe :=
  ⟨hacyclic, Subgraph.IsMatching.isAlternating_symmDiff_left hM hM'⟩

end SimpleGraph
end AutocatalyticCS
