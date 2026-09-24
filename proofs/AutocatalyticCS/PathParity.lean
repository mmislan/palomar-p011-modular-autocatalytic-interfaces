import proofs.AutocatalyticCS.CycleToggle
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
Parity of the nontrivial components in a matching exchange.  The first and
last edges at external vertices belong to the outer matching; alternation
therefore forces an odd number of edges.  In a species--reaction bipartite
graph, odd length is exactly the assertion that the two endpoints have
opposite types.
-/

open scoped symmDiff

namespace AutocatalyticCS
namespace SimpleGraph

open _root_.SimpleGraph

variable {V : Type*}

theorem odd_length_cons_of_alternating_of_not_reference_at_ends
    {P reference : _root_.SimpleGraph V} (halt : P.IsAlternating reference)
    {u x v : V} (hux : P.Adj u x) (q : P.Walk x v)
    (hp : (Walk.cons hux q).IsPath) (hfirst : ¬reference.Adj u x)
    (hlast : ∀ ⦃w⦄, P.Adj v w → ¬reference.Adj v w) :
    Odd (Walk.cons hux q).length := by
  cases q with
  | nil => simp
  | @cons x y v hxy r =>
      have huy : u ≠ y := by
        have hu : u ∉ (Walk.cons hxy r).support :=
          (Walk.cons_isPath_iff hux (Walk.cons hxy r)).mp hp |>.2
        intro heq
        apply hu
        simp [heq]
      have hmiddle : reference.Adj x y := by
        have htoggle := halt huy hux.symm hxy
        have hn : ¬reference.Adj x u := fun h => hfirst h.symm
        tauto
      cases r with
      | nil =>
          exact (hlast hxy.symm hmiddle.symm).elim
      | @cons y z v hyz s =>
          have hxz : x ≠ z := by
            have hx : x ∉ (Walk.cons hyz s).support :=
              (Walk.cons_isPath_iff hxy (Walk.cons hyz s)).mp hp.of_cons |>.2
            intro heq
            apply hx
            simp [heq]
          have hthird : ¬reference.Adj y z := by
            have htoggle := halt hxz hxy.symm hyz
            have hm : reference.Adj y x := hmiddle.symm
            tauto
          have hp' : (Walk.cons hyz s).IsPath := hp.of_cons.of_cons
          have hodd :=
            odd_length_cons_of_alternating_of_not_reference_at_ends
              halt hyz s hp' hthird hlast
          simpa [Walk.length_cons, Nat.odd_add] using hodd
termination_by q.length

def sumBicoloring {X R : Type*} {P : _root_.SimpleGraph (X ⊕ R)}
    (hbip : P.IsBipartiteWith {v | v.isLeft} {v | v.isRight}) :
    P.Coloring Bool :=
  Coloring.mk (fun v => match v with | Sum.inl _ => true | Sum.inr _ => false) (by
    intro u v huv
    rcases hbip.mem_of_adj huv with h | h <;>
      rcases u with u | u <;> rcases v with v | v <;> simp_all)

@[simp] theorem sumBicoloring_inl {X R : Type*}
    {P : _root_.SimpleGraph (X ⊕ R)}
    (hbip : P.IsBipartiteWith {v | v.isLeft} {v | v.isRight}) (x : X) :
    sumBicoloring hbip (Sum.inl x) = true := rfl

@[simp] theorem sumBicoloring_inr {X R : Type*}
    {P : _root_.SimpleGraph (X ⊕ R)}
    (hbip : P.IsBipartiteWith {v | v.isLeft} {v | v.isRight}) (r : R) :
    sumBicoloring hbip (Sum.inr r) = false := rfl

theorem odd_path_has_opposite_sum_endpoints {X R : Type*}
    {P : _root_.SimpleGraph (X ⊕ R)}
    (hbip : P.IsBipartiteWith {v | v.isLeft} {v | v.isRight})
    {u v : X ⊕ R} (p : P.Walk u v) (hodd : Odd p.length) :
    (u.isLeft ∧ v.isRight) ∨ (u.isRight ∧ v.isLeft) := by
  have hcolors := ((sumBicoloring hbip).odd_length_iff_not_congr p).mp hodd
  rcases u with u | u <;> rcases v with v | v
  · simp at hcolors
  · simp
  · simp
  · simp at hcolors

/-- Every nonempty simple exchange path whose endpoints are external to the
inner matching connects opposite sides of the species--reaction bipartition. -/
theorem exchangePath_has_external_opposite_endpoints {X R : Type*}
    {A : _root_.SimpleGraph (X ⊕ R)} {M M' : A.Subgraph}
    (hM : M.IsMatching) (hM' : M'.IsMatching)
    (hbip : A.IsBipartiteWith {v | v.isLeft} {v | v.isRight})
    {u v : X ⊕ R} (p : (M.spanningCoe ∆ M'.spanningCoe).Walk u v)
    (hp : p.IsPath) (hnon : ¬p.Nil) (hu : u ∉ M.verts) (hv : v ∉ M.verts) :
    (u.isLeft ∧ v.isRight) ∨ (u.isRight ∧ v.isLeft) := by
  have hne : u ≠ v := by
    intro huv
    subst v
    exact hnon (_root_.SimpleGraph.Walk.eq_nil_iff_nil.mp
      ((_root_.SimpleGraph.Walk.isPath_iff_eq_nil p).mp hp))
  obtain ⟨x, hux, q, hpq⟩ :=
    _root_.SimpleGraph.Walk.exists_eq_cons_of_ne hne p
  subst p
  have hfirst : ¬M.spanningCoe.Adj u x := by
    intro h
    exact hu (M.edge_vert (by simpa using h))
  have hlast : ∀ ⦃w⦄,
      (M.spanningCoe ∆ M'.spanningCoe).Adj v w → ¬M.spanningCoe.Adj v w := by
    intro w _ h
    exact hv (M.edge_vert (by simpa using h))
  have hodd : Odd (Walk.cons hux q).length :=
    odd_length_cons_of_alternating_of_not_reference_at_ends
      (Subgraph.IsMatching.isAlternating_symmDiff_left hM hM')
      hux q hp hfirst hlast
  have hsub : M.spanningCoe ∆ M'.spanningCoe ≤ A := by
    intro a b hab
    simp only [symmDiff_def, _root_.SimpleGraph.sup_adj,
      _root_.SimpleGraph.sdiff_adj, Subgraph.spanningCoe_adj] at hab
    rcases hab with hab | hab
    · exact M.adj_sub hab.1
    · exact M'.adj_sub hab.1
  have hbip' : (M.spanningCoe ∆ M'.spanningCoe).IsBipartiteWith
      {v | v.isLeft} {v | v.isRight} := by
    refine ⟨hbip.disjoint, ?_⟩
    intro a b h
    exact hbip.mem_of_adj (hsub h)
  exact odd_path_has_opposite_sum_endpoints hbip' (Walk.cons hux q) hodd

def IsExternalBipartitePathPack {X R : Type*}
    (P reference : _root_.SimpleGraph (X ⊕ R)) (inner : Set (X ⊕ R)) : Prop :=
  IsAlternatingPathPack P reference ∧ HasExternalEndpoints P inner ∧
    ∀ ⦃u v⦄ (p : P.Walk u v), p.IsPath → ¬p.Nil →
      u ∉ inner → v ∉ inner →
      (u.isLeft ∧ v.isRight) ∨ (u.isRight ∧ v.isLeft)

/-- Exact exchange-decomposition interface.  Acyclicity plus alternating
degree at most two makes the exchange graph a vertex-disjoint path family;
the second conjunct identifies precisely its external endpoints, and the
third gives their species/reaction types. -/
theorem exchange_isExternalBipartitePathPack_of_unique_left {X R : Type*}
    {A : _root_.SimpleGraph (X ⊕ R)} {M M' : A.Subgraph}
    (hunique : Subgraph.IsUniqueMatching M) (hM' : M'.IsMatching)
    (hverts : M.verts ⊆ M'.verts)
    (hbip : A.IsBipartiteWith {v | v.isLeft} {v | v.isRight}) :
    IsExternalBipartitePathPack (M.spanningCoe ∆ M'.spanningCoe)
      M.spanningCoe M.verts := by
  refine ⟨exchange_isExternalEndpointPathPack_of_unique_left
    hunique hM' hverts |>.1, ?_, ?_⟩
  · exact exchange_isExternalEndpointPathPack_of_unique_left
      hunique hM' hverts |>.2
  · intro u v p hp hnon hu hv
    exact exchangePath_has_external_opposite_endpoints
      hunique.1 hM' hbip p hp hnon hu hv

end SimpleGraph
end AutocatalyticCS
