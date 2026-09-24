import proofs.AutocatalyticCS.SourceGraphBridge
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Finite tree endpoint lemmas needed for extracting exchange paths. -/

namespace AutocatalyticCS

open _root_.SimpleGraph

variable {V : Type*} {G : _root_.SimpleGraph V}

/-- Restricting to a connected component does not lose any neighbor of a
vertex in that component. -/
def SimpleGraph.ConnectedComponent.neighborEquiv
    (c : G.ConnectedComponent) (v : c) :
    c.toSimpleGraph.neighborSet v ≃ G.neighborSet v.1 where
  toFun w := ⟨w.1.1, by
    rw [mem_neighborSet]
    exact (c.toSimpleGraph_adj v.2 w.1.2).mp w.2⟩
  invFun w := ⟨⟨w.1, c.mem_supp_congr_adj w.2 |>.mp v.2⟩, by
    rw [mem_neighborSet, c.toSimpleGraph_adj]
    exact w.2⟩
  left_inv w := by ext; rfl
  right_inv w := by ext; rfl

theorem SimpleGraph.ConnectedComponent.degree_toSimpleGraph
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (c : G.ConnectedComponent) [Fintype c]
    [DecidableRel c.toSimpleGraph.Adj] (v : c) :
    c.toSimpleGraph.degree v = G.degree v.1 := by
  rw [← c.toSimpleGraph.card_neighborSet_eq_degree,
    ← G.card_neighborSet_eq_degree]
  exact Fintype.card_congr (SimpleGraph.ConnectedComponent.neighborEquiv c v)

/-- A finite tree of maximum degree two has a second leaf distinct from any
specified leaf.  This arithmetic form avoids choosing a traversal. -/
theorem SimpleGraph.IsTree.exists_other_degree_one
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hT : G.IsTree) (s : V) (hs : G.degree s = 1)
    (hmax : ∀ v, G.degree v ≤ 2) :
    ∃ t, t ≠ s ∧ G.degree t = 1 := by
  haveI : Nontrivial V := by
    rw [degree_eq_one_iff_existsUnique_adj] at hs
    obtain ⟨w, hsw, _⟩ := hs
    exact ⟨⟨s, w, hsw.ne⟩⟩
  by_contra h
  push Not at h
  have hdegree : ∀ v, G.degree v = if v = s then 1 else 2 := by
    intro v
    by_cases hvs : v = s
    · subst v
      simp [hs]
    · have hpos : 0 < G.degree v := hT.preconnected.degree_pos_of_nontrivial v
      have hneone : G.degree v ≠ 1 := h v hvs
      have hle := hmax v
      simp [hvs]
      omega
  have hsum : ∑ v, G.degree v = 2 * Fintype.card V - 1 := by
    calc
      ∑ v, G.degree v = ∑ v, if v = s then 1 else 2 := by
        apply Finset.sum_congr rfl
        intro v _
        exact hdegree v
      _ = 2 * Fintype.card V - 1 := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ s)]
        have herase :
            ∑ x ∈ Finset.univ.erase s, (if x = s then 1 else 2) =
              ∑ _x ∈ Finset.univ.erase s, 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [Finset.mem_erase.mp hx |>.1]
        rw [herase]
        have hconst :
            (∑ _x ∈ Finset.univ.erase s, 2) =
              2 * (Fintype.card V - 1) := by
          simp [Finset.card_erase_of_mem, Nat.mul_comm]
        rw [hconst]
        simp
        have hcard : 0 < Fintype.card V := Fintype.card_pos
        omega
  have hedges := hT.card_edgeFinset
  have hhandshake := G.sum_degrees_eq_twice_card_edges
  rw [hsum] at hhandshake
  omega

/-- Every supported external vertex of a finite alternating acyclic graph lies
on a nontrivial simple path to a second external vertex. -/
theorem SimpleGraph.IsAlternatingPathPack.exists_path_to_other_external
    {P reference : _root_.SimpleGraph V} {inner : Set V}
    [Fintype V] [DecidableEq V] [DecidableRel P.Adj]
    (hpack : SimpleGraph.IsAlternatingPathPack P reference)
    (hend : SimpleGraph.HasExternalEndpoints P inner)
    {s : V} (hsupport : s ∈ P.support) (hsext : s ∉ inner) :
    ∃ t, t ≠ s ∧ t ∉ inner ∧ ∃ p : P.Walk s t, p.IsPath := by
  classical
  let c := P.connectedComponentMk s
  letI : Fintype c := Fintype.ofFinite c
  letI : DecidableRel c.toSimpleGraph.Adj := Classical.decRel _
  let s' : c := ⟨s, by
    exact ConnectedComponent.connectedComponentMk_mem⟩
  have hsone : c.toSimpleGraph.degree s' = 1 := by
    rw [SimpleGraph.ConnectedComponent.degree_toSimpleGraph]
    exact degree_eq_one_iff_existsUnique_adj.mpr ((hend hsupport).mpr hsext)
  have hmax : ∀ v, c.toSimpleGraph.degree v ≤ 2 := by
    intro v
    rw [SimpleGraph.ConnectedComponent.degree_toSimpleGraph]
    have hn :=
      AutocatalyticCS.SimpleGraph.IsAlternating.ncard_neighborSet_le_two
        hpack.2 v.1
    rw [Set.ncard_eq_toFinset_card'] at hn
    exact hn
  have htree : c.toSimpleGraph.IsTree := hpack.1.isTree_connectedComponent c
  obtain ⟨t', hts, htdegree⟩ :=
    AutocatalyticCS.SimpleGraph.IsTree.exists_other_degree_one
      htree s' hsone hmax
  have htdegreeP : P.degree t'.1 = 1 := by
    rw [← SimpleGraph.ConnectedComponent.degree_toSimpleGraph c t']
    exact htdegree
  have htsupport : t'.1 ∈ P.support := by
    rw [← P.degree_pos_iff_mem_support]
    omega
  have htext : t'.1 ∉ inner :=
    (hend htsupport).mp (degree_eq_one_iff_existsUnique_adj.mp htdegreeP)
  obtain ⟨p, hp⟩ := htree.preconnected.exists_isPath s' t'
  refine ⟨t'.1, ?_, htext, p.map c.toSimpleGraph_hom, ?_⟩
  · intro h
    exact hts (Subtype.ext h)
  · exact _root_.SimpleGraph.Walk.map_isPath_of_injective
      Subtype.val_injective hp

/-- An internal vertex of a simple path cannot have a unique neighbor in the
ambient graph: its predecessor and successor are distinct ambient neighbors. -/
theorem SimpleGraph.Walk.IsPath.not_existsUnique_adj_of_internal
    {u v w : V} (p : G.Walk u v) (hp : p.IsPath)
    (hw : w ∈ p.support) (hwu : w ≠ u) (hwv : w ≠ v) :
    ¬∃! z, G.Adj w z := by
  rw [_root_.SimpleGraph.Walk.mem_support_iff_exists_getVert] at hw
  obtain ⟨n, hn, hnle⟩ := hw
  subst w
  have hnzero : n ≠ 0 := by
    intro hn0
    subst n
    exact hwu (by simp)
  have hnlt : n < p.length := by
    apply lt_of_le_of_ne hnle
    intro hneq
    apply hwv
    rw [hneq]
    simp
  have hcard := hp.ncard_neighborSet_toSubgraph_internal_eq_two hnzero hnlt
  obtain ⟨a, b, hab, hset⟩ := Set.ncard_eq_two.mp hcard
  intro hunique
  apply hab
  apply hunique.unique
  · apply p.toSubgraph.adj_sub
    rw [← _root_.SimpleGraph.Subgraph.mem_neighborSet, hset]
    simp
  · apply p.toSubgraph.adj_sub
    rw [← _root_.SimpleGraph.Subgraph.mem_neighborSet, hset]
    simp

/-- In a finite alternating path forest, a simple path between two external
endpoints contains its entire connected component. -/
theorem SimpleGraph.IsAlternatingPathPack.path_spans_connectedComponent
    {P reference : _root_.SimpleGraph V} {inner : Set V}
    [Fintype V] [DecidableEq V] [DecidableRel P.Adj]
    (hpack : SimpleGraph.IsAlternatingPathPack P reference)
    (hend : SimpleGraph.HasExternalEndpoints P inner)
    {u v : V} (p : P.Walk u v) (hp : p.IsPath) (hnon : ¬p.Nil)
    (huext : u ∉ inner) (hvext : v ∉ inner) :
    ∃ c : P.ConnectedComponent, p.toSubgraph.verts = c.supp ∧
      ∀ z ∈ c.supp, ∀ w, P.Adj z w → p.toSubgraph.Adj z w := by
  classical
  have hclosed : ∀ z ∈ p.toSubgraph.verts, ∀ w,
      P.Adj z w → p.toSubgraph.Adj z w := by
    intro z hz w hzw
    rw [_root_.SimpleGraph.Walk.mem_verts_toSubgraph,
      _root_.SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
    obtain ⟨n, hn, hnle⟩ := hz
    subst z
    by_cases hnzero : n = 0
    · subst n
      have hpath : p.toSubgraph.Adj u p.snd := p.toSubgraph_adj_snd hnon
      have huSupport : u ∈ P.support := (p.toSubgraph.adj_sub hpath).mem_support_left
      have huUnique := (hend huSupport).mpr huext
      have hzw' : P.Adj u w := by simpa using hzw
      have hw : w = p.snd := huUnique.unique hzw' (p.toSubgraph.adj_sub hpath)
      simpa [hw] using hpath
    · by_cases hnlength : n = p.length
      · subst n
        have hpath : p.toSubgraph.Adj p.penultimate v :=
          p.toSubgraph_adj_penultimate hnon
        have hvSupport : v ∈ P.support := (p.toSubgraph.adj_sub hpath).mem_support_right
        have hvUnique := (hend hvSupport).mpr hvext
        have hzw' : P.Adj v w := by simpa using hzw
        have hw : w = p.penultimate :=
          hvUnique.unique hzw' (p.toSubgraph.adj_sub hpath).symm
        simpa [hw] using hpath.symm
      · have hnlt : n < p.length := lt_of_le_of_ne hnle hnlength
        have hsubset : p.toSubgraph.neighborSet (p.getVert n) ⊆
            P.neighborSet (p.getVert n) := by
          intro a ha
          exact p.toSubgraph.adj_sub ha
        have hpathcard :
            (p.toSubgraph.neighborSet (p.getVert n)).ncard = 2 :=
          hp.ncard_neighborSet_toSubgraph_internal_eq_two hnzero hnlt
        have hambientcard : (P.neighborSet (p.getVert n)).ncard ≤ 2 :=
          SimpleGraph.IsAlternating.ncard_neighborSet_le_two hpack.2 _
        have hsets : p.toSubgraph.neighborSet (p.getVert n) =
            P.neighborSet (p.getVert n) :=
          Set.eq_of_subset_of_ncard_le hsubset (by omega)
        rw [← _root_.SimpleGraph.Subgraph.mem_neighborSet, hsets]
        exact hzw
  obtain ⟨c, hc⟩ :=
    p.toSubgraph_connected.exists_verts_eq_connectedComponentSupp hclosed
  refine ⟨c, hc, ?_⟩
  intro z hz
  exact hclosed z (hc ▸ hz)

/-- Every edge of a finite external bipartite path pack lies on a simple path
whose first endpoint is an external left vertex and whose last endpoint is an
external right vertex. -/
theorem SimpleGraph.IsExternalBipartitePathPack.exists_path_covering_adj
    {X R : Type*} {P reference : _root_.SimpleGraph (X ⊕ R)}
    {inner : Set (X ⊕ R)}
    [Fintype X] [Fintype R] [DecidableEq X] [DecidableEq R]
    [DecidableRel P.Adj]
    (hprofile : SimpleGraph.IsExternalBipartitePathPack P reference inner)
    {a b : X ⊕ R} (hab : P.Adj a b) :
    ∃ x r, ∃ p : P.Walk (Sum.inl x) (Sum.inr r),
      Sum.inl x ∉ inner ∧ Sum.inr r ∉ inner ∧ p.IsPath ∧
        p.toSubgraph.Adj a b := by
  classical
  let c := P.connectedComponentMk a
  letI : Fintype c := Fintype.ofFinite c
  letI : DecidableRel c.toSimpleGraph.Adj := Classical.decRel _
  haveI : Nontrivial c := by
    refine ⟨⟨⟨a, ConnectedComponent.connectedComponentMk_mem⟩,
      ⟨b, (c.mem_supp_congr_adj hab).mp
        ConnectedComponent.connectedComponentMk_mem⟩, ?_⟩⟩
    exact fun h ↦ hab.ne (Subtype.ext_iff.mp h)
  have htree : c.toSimpleGraph.IsTree :=
    hprofile.1.1.isTree_connectedComponent c
  obtain ⟨s, hsdegree⟩ := htree.exists_vert_degree_one_of_nontrivial
  have hsdegreeP : P.degree s.1 = 1 := by
    rw [← SimpleGraph.ConnectedComponent.degree_toSimpleGraph c s]
    exact hsdegree
  have hssupport : s.1 ∈ P.support := by
    rw [← P.degree_pos_iff_mem_support]
    omega
  have hsexternal : s.1 ∉ inner :=
    (hprofile.2.1 hssupport).mp
      (degree_eq_one_iff_existsUnique_adj.mp hsdegreeP)
  obtain ⟨t, hts, htexternal, p, hp⟩ :=
    hprofile.1.exists_path_to_other_external hprofile.2.1
      hssupport hsexternal
  have hpnon : ¬p.Nil := by
    intro hnil
    exact hts hnil.eq.symm
  obtain ⟨d, hdverts, hdclosed⟩ :=
    hprofile.1.path_spans_connectedComponent hprofile.2.1 p hp hpnon
      hsexternal htexternal
  have hsd : s.1 ∈ d.supp := by
    rw [← hdverts, _root_.SimpleGraph.Walk.mem_verts_toSubgraph]
    exact p.start_mem_support
  have hdc : d = c := by
    rw [ConnectedComponent.mem_supp_iff] at hsd
    have hsc : P.connectedComponentMk s.1 = c :=
      (ConnectedComponent.mem_supp_iff c s.1).mp s.2
    exact hsd.symm.trans hsc
  have hcover : p.toSubgraph.Adj a b := by
    apply hdclosed a
    · rw [hdc]
      exact ConnectedComponent.connectedComponentMk_mem
    · exact hab
  rcases hprofile.2.2 p hp hpnon hsexternal htexternal with hst | hst
  · cases hsval : s.1 with
    | inl x =>
      cases htval : t with
      | inl y => simp [hsval, htval] at hst
      | inr q =>
        let p' : P.Walk (Sum.inl x) (Sum.inr q) := p.copy hsval htval
        refine ⟨x, q, p', ?_, ?_, ?_, ?_⟩
        · simpa [hsval] using hsexternal
        · simpa [htval] using htexternal
        · simpa [p'] using hp
        · rw [_root_.SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
          simpa [p'] using
            (_root_.SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp hcover)
    | inr r => simp [hsval] at hst
  · cases hsval : s.1 with
    | inl x => simp [hsval] at hst
    | inr r =>
      cases htval : t with
      | inl y =>
        let p' : P.Walk (Sum.inl y) (Sum.inr r) :=
          p.reverse.copy htval hsval
        refine ⟨y, r, p', ?_, ?_, ?_, ?_⟩
        · simpa [htval] using htexternal
        · simpa [hsval] using hsexternal
        · simpa [p'] using hp.reverse
        · rw [_root_.SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
          simpa [p'] using
            (_root_.SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp hcover)
      | inr q => simp [htval] at hst

end AutocatalyticCS
