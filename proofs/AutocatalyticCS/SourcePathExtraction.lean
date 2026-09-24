import proofs.AutocatalyticCS.FinitePathForest

/-! Extract source-typed paths from a concrete matching exchange profile. -/

namespace AutocatalyticCS

open _root_.SimpleGraph
open scoped symmDiff

variable {X R : Type*} [Fintype X] [Fintype R]
variable [DecidableEq X] [DecidableEq R]
variable {Q : ReactionNetwork X R}

def SourceEdgeExpected (reference : _root_.SimpleGraph (X ⊕ R)) :
    (X ⊕ R) → (X ⊕ R) → Prop
  | u@(Sum.inl _), w => ¬reference.Adj u w
  | u@(Sum.inr _), w => reference.Adj u w

def FirstSourceEdgeExpected (reference : _root_.SimpleGraph (X ⊕ R)) :
    {P : _root_.SimpleGraph (X ⊕ R)} → {u v : X ⊕ R} →
      P.Walk u v → Prop := fun p =>
  match p.darts with
  | [] => True
  | d :: _ => SourceEdgeExpected reference d.fst d.snd

omit [Fintype X] [Fintype R] in
/-- Alternation plus the expected first edge orients an entire bipartite walk
according to the source successor table. -/
theorem sourceFollows_of_firstExpected
    {P : _root_.SimpleGraph (X ⊕ R)} {anchor : IndexedMatching Q}
    (reactionOrder : List R) (hreactions : ∀ r, r ∈ reactionOrder)
    (hsub : P ≤ reactantGraph Q)
    (halt : P.IsAlternating anchor.subgraph.spanningCoe)
    {u v : X ⊕ R} (p : P.Walk u v) (hp : p.IsPath)
    (hfirst : FirstSourceEdgeExpected anchor.subgraph.spanningCoe p) :
    Follows (sourceExchangeNext Q anchor reactionOrder) p.support := by
  induction p with
  | nil => simp [Follows]
  | @cons u w v huw q ih =>
      have hpq : q.IsPath := hp.of_cons
      have huq : u ∉ q.support :=
        (_root_.SimpleGraph.Walk.cons_isPath_iff huw q).mp hp |>.2
      have hstep : w ∈ sourceExchangeNext Q anchor reactionOrder u := by
        have hambient := hsub huw
        cases u with
        | inl x =>
            cases w with
            | inl y => exact hambient.elim
            | inr r =>
                rw [mem_sourceExchangeNext_inl_iff]
                exact ⟨hreactions r, hambient⟩
        | inr r =>
            cases w with
            | inl x =>
                rw [mem_sourceExchangeNext_inr_iff,
                  IndexedMatching.mem_edgeList_iff]
                simpa [FirstSourceEdgeExpected, SourceEdgeExpected,
                  IndexedMatching.subgraph] using hfirst
            | inr s => exact hambient.elim
      have hfirstq : FirstSourceEdgeExpected anchor.subgraph.spanningCoe q := by
        cases q with
        | nil => simp [FirstSourceEdgeExpected]
        | @cons w z v hwz tail =>
            have huz : u ≠ z := by
              intro huz
              subst z
              exact huq (by simp)
            have htoggle := halt huz huw.symm hwz
            have huambient := hsub huw
            have hwambient := hsub hwz
            cases u with
            | inl x =>
                cases w with
                | inl y => exact huambient.elim
                | inr r =>
                    cases z with
                    | inl x' =>
                        change anchor.subgraph.Adj (Sum.inr r) (Sum.inl x')
                        by_contra hn
                        have hback : anchor.subgraph.Adj
                            (Sum.inr r) (Sum.inl x) := htoggle.mpr hn
                        exact hfirst hback.symm
                    | inr r' => exact hwambient.elim
            | inr r =>
                cases w with
                | inl x =>
                    cases z with
                    | inl x' => exact hwambient.elim
                    | inr r' =>
                        change ¬anchor.subgraph.Adj (Sum.inl x) (Sum.inr r')
                        have hback : anchor.subgraph.Adj
                            (Sum.inl x) (Sum.inr r) := hfirst.symm
                        exact htoggle.mp hback
                | inr r' => exact huambient.elim
      have htail := ih hpq hfirstq
      cases q <;> simpa [Follows] using And.intro hstep htail

omit [Fintype X] [Fintype R] in
/-- The expected first exchange edge and graph alternation orient every edge:
species-to-reaction steps are non-anchor edges and reaction-to-species steps
are anchor edges. -/
theorem sourceOriented_of_firstExpected
    {P : _root_.SimpleGraph (X ⊕ R)} {anchor : IndexedMatching Q}
    (hsub : P ≤ reactantGraph Q)
    (halt : P.IsAlternating anchor.subgraph.spanningCoe)
    {u v : X ⊕ R} (p : P.Walk u v) (hp : p.IsPath)
    (hfirst : FirstSourceEdgeExpected anchor.subgraph.spanningCoe p) :
    SourceOriented anchor.subgraph.spanningCoe p.support := by
  induction p with
  | nil => simp [SourceOriented, forwardEdges, backwardEdges]
  | @cons u w v huw q ih =>
      have hpq : q.IsPath := hp.of_cons
      have huq : u ∉ q.support :=
        (_root_.SimpleGraph.Walk.cons_isPath_iff huw q).mp hp |>.2
      have hfirstq : FirstSourceEdgeExpected anchor.subgraph.spanningCoe q := by
        cases q with
        | nil => simp [FirstSourceEdgeExpected]
        | @cons w z v hwz tail =>
            have huz : u ≠ z := by
              intro huz
              subst z
              exact huq (by simp)
            have htoggle := halt huz huw.symm hwz
            have huambient := hsub huw
            have hwambient := hsub hwz
            cases u with
            | inl x =>
                cases w with
                | inl y => exact huambient.elim
                | inr r =>
                    cases z with
                    | inl x' =>
                        change anchor.subgraph.Adj (Sum.inr r) (Sum.inl x')
                        by_contra hn
                        have hback : anchor.subgraph.Adj
                            (Sum.inr r) (Sum.inl x) := htoggle.mpr hn
                        exact hfirst hback.symm
                    | inr r' => exact hwambient.elim
            | inr r =>
                cases w with
                | inl x =>
                    cases z with
                    | inl x' => exact hwambient.elim
                    | inr r' =>
                        change ¬anchor.subgraph.Adj (Sum.inl x) (Sum.inr r')
                        have hback : anchor.subgraph.Adj
                            (Sum.inl x) (Sum.inr r) := hfirst.symm
                        exact htoggle.mp hback
                | inr r' => exact huambient.elim
      have htail := ih hpq hfirstq
      apply SourceOriented.cons_walk huw q htail
      · intro x r hu hw
        subst u
        subst w
        exact hfirst
      · intro r x hu hw
        subst u
        subst w
        exact hfirst.symm

/-- An external species occurring in the symmetric-difference support is the
start of a simple exchange path ending at an external reaction. -/
theorem source_exists_exchange_path_to_external_reaction
    {anchor target : IndexedMatching Q}
    (hunique : SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (hcontains : anchor.VertexContained target)
    {x : X}
    (hsupport : Sum.inl x ∈
      (anchor.subgraph.spanningCoe ∆ target.subgraph.spanningCoe).support)
    (hxext : x ∉ anchor.species) :
    ∃ r, r ∉ anchor.reactions ∧
      ∃ p : (anchor.subgraph.spanningCoe ∆ target.subgraph.spanningCoe).Walk
        (Sum.inl x) (Sum.inr r), p.IsPath := by
  classical
  let P := anchor.subgraph.spanningCoe ∆ target.subgraph.spanningCoe
  have hprofile := source_exchange_profile hunique hcontains
  have hxinner : Sum.inl x ∉ anchor.subgraph.verts := hxext
  obtain ⟨t, hts, htext, p, hp⟩ :=
    AutocatalyticCS.SimpleGraph.IsAlternatingPathPack.exists_path_to_other_external
      hprofile.1 hprofile.2.1 hsupport hxinner
  have hpnon : ¬p.Nil := by
    intro hnil
    exact hts hnil.eq.symm
  have hopposite := hprofile.2.2 p hp hpnon hxinner htext
  rcases t with y | r
  · simp at hopposite
  · refine ⟨r, ?_, p, hp⟩
    exact htext

omit [Fintype X] [Fintype R] in
/-- Along an exchange path between external endpoints, no reaction before the
last vertex is a source-level boundary target.  Otherwise that internal
reaction would simultaneously have degree one (by the endpoint profile) and
two distinct path neighbors. -/
theorem source_exchange_path_internal_target_false
    {anchor target : IndexedMatching Q}
    (hunique : SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (hcontains : anchor.VertexContained target)
    {x : X} {r : R}
    (p : (anchor.subgraph.spanningCoe ∆ target.subgraph.spanningCoe).Walk
      (Sum.inl x) (Sum.inr r))
    (hp : p.IsPath) :
    ∀ w ∈ p.support, w ≠ Sum.inr r →
      sourceBoundaryTarget anchor w = false := by
  classical
  let P := anchor.subgraph.spanningCoe ∆ target.subgraph.spanningCoe
  have hprofile := source_exchange_profile hunique hcontains
  intro w hw hwend
  cases w with
  | inl y => rfl
  | inr s =>
      have hs : s ∈ anchor.reactions := by
        by_contra hsext
        have hwstart : Sum.inr s ≠ Sum.inl x := by simp
        have hwPsupport : Sum.inr s ∈ P.support := by
          rw [_root_.SimpleGraph.Walk.mem_support_iff_exists_getVert] at hw
          obtain ⟨n, hn, hnle⟩ := hw
          have hnzero : n ≠ 0 := by
            intro hn0
            subst n
            exact hwstart (by simpa using hn.symm)
          have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
          have hadj : P.Adj (p.getVert n) (p.getVert (n - 1)) := by
            simpa [Nat.sub_add_cancel hnpos] using
              (p.adj_getVert_succ (i := n - 1) (by omega)).symm
          rw [← hn]
          exact hadj.mem_support_left
        have huniqueNeighbor : ∃! z, P.Adj (Sum.inr s) z :=
          (hprofile.2.1 hwPsupport).mpr hsext
        exact
          (AutocatalyticCS.SimpleGraph.Walk.IsPath.not_existsUnique_adj_of_internal
            p hp hw hwstart hwend) huniqueNeighbor
      simp [sourceBoundaryTarget, hs]

omit [Fintype X] [Fintype R] in
theorem source_exchange_path_sourceOriented
    {anchor target : IndexedMatching Q}
    (hunique : SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (hcontains : anchor.VertexContained target)
    {x : X} (hxext : x ∉ anchor.species) {r : R}
    (p : (anchor.subgraph.spanningCoe ∆ target.subgraph.spanningCoe).Walk
      (Sum.inl x) (Sum.inr r))
    (hp : p.IsPath) :
    SourceOriented anchor.subgraph.spanningCoe p.support := by
  classical
  let P := anchor.subgraph.spanningCoe ∆ target.subgraph.spanningCoe
  have hprofile := source_exchange_profile hunique hcontains
  have hsub : P ≤ reactantGraph Q := by
    change anchor.subgraph.spanningCoe ∆ target.subgraph.spanningCoe ≤
      reactantGraph Q
    intro a b hab
    simp only [symmDiff_def, _root_.SimpleGraph.sup_adj,
      _root_.SimpleGraph.sdiff_adj, Subgraph.spanningCoe_adj] at hab
    rcases hab with hab | hab
    · exact anchor.subgraph.adj_sub hab.1
    · exact target.subgraph.adj_sub hab.1
  have hfirst : FirstSourceEdgeExpected anchor.subgraph.spanningCoe p := by
    have hne : Sum.inl x ≠ Sum.inr r := by simp
    obtain ⟨w, hxw, q, hpq⟩ :=
      _root_.SimpleGraph.Walk.exists_eq_cons_of_ne hne p
    subst p
    change SourceEdgeExpected anchor.subgraph.spanningCoe (Sum.inl x) w
    cases w with
    | inl y => exact (hsub hxw).elim
    | inr s =>
        change ¬anchor.subgraph.Adj (Sum.inl x) (Sum.inr s)
        intro ha
        exact hxext (anchor.subgraph.edge_vert ha)
  exact sourceOriented_of_firstExpected hsub hprofile.1.2 p hp hfirst

/-- Every correctly oriented exchange path is literally emitted by the finite
source DFS.  Thus the executable search does not merely approximate the
graph-theoretic path witness. -/
theorem source_exchange_path_mem_directBoundaryPaths
    {anchor target : IndexedMatching Q}
    (hunique : SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (hcontains : anchor.VertexContained target)
    (speciesOrder : List X) (hspecies : ∀ x, x ∈ speciesOrder)
    (reactionOrder : List R) (hreactions : ∀ r, r ∈ reactionOrder)
    {x : X} (hxext : x ∉ anchor.species) {r : R}
    (hrext : r ∉ anchor.reactions)
    (p : (anchor.subgraph.spanningCoe ∆ target.subgraph.spanningCoe).Walk
      (Sum.inl x) (Sum.inr r))
    (hp : p.IsPath) :
    p.support ∈ directBoundaryPaths
      (sourceExchangeNext Q anchor reactionOrder)
      (sourceBoundaryTarget anchor)
      (sourceBoundaryStarts anchor speciesOrder) := by
  classical
  let P := anchor.subgraph.spanningCoe ∆ target.subgraph.spanningCoe
  have hprofile := source_exchange_profile hunique hcontains
  have hsub : P ≤ reactantGraph Q := by
    change anchor.subgraph.spanningCoe ∆ target.subgraph.spanningCoe ≤
      reactantGraph Q
    intro a b hab
    simp only [symmDiff_def, _root_.SimpleGraph.sup_adj,
      _root_.SimpleGraph.sdiff_adj, Subgraph.spanningCoe_adj] at hab
    rcases hab with hab | hab
    · exact anchor.subgraph.adj_sub hab.1
    · exact target.subgraph.adj_sub hab.1
  have hfirst : FirstSourceEdgeExpected anchor.subgraph.spanningCoe p := by
    have hne : Sum.inl x ≠ Sum.inr r := by simp
    obtain ⟨w, hxw, q, hpq⟩ :=
      _root_.SimpleGraph.Walk.exists_eq_cons_of_ne hne p
    subst p
    change SourceEdgeExpected anchor.subgraph.spanningCoe (Sum.inl x) w
    cases w with
    | inl y => exact (hsub hxw).elim
    | inr s =>
        change ¬anchor.subgraph.Adj (Sum.inl x) (Sum.inr s)
        intro ha
        exact hxext (anchor.subgraph.edge_vert ha)
  have hfollow : Follows (sourceExchangeNext Q anchor reactionOrder) p.support :=
    sourceFollows_of_firstExpected reactionOrder hreactions hsub
      hprofile.1.2 p hp hfirst
  have htarget : sourceBoundaryTarget anchor (Sum.inr r) = true :=
    (sourceBoundaryTarget_inr_eq_true_iff anchor r).2 hrext
  have hinternal : ∀ w ∈ p.support, w ≠ Sum.inr r →
      sourceBoundaryTarget anchor w = false :=
    source_exchange_path_internal_target_false hunique hcontains p hp
  have hdirect : IsDirectPath (sourceExchangeNext Q anchor reactionOrder)
      (sourceBoundaryTarget anchor) (Fintype.card (X ⊕ R)) []
      (Sum.inl x) p.support :=
    isDirectPath_support_of_walk _ _ p hp hfollow htarget hinternal _ _
      (Nat.le_of_lt hp.length_lt) (by simp)
  rw [mem_directBoundaryPaths_iff]
  exact ⟨Sum.inl x,
    (mem_sourceBoundaryStarts_iff anchor speciesOrder x).2
      ⟨hspecies x, hxext⟩,
    hdirect⟩

omit [Fintype X] [Fintype R] in
/-- A symmetric-difference component contains at most one anchor-external
species.  Two such species would be joined by a nontrivial external-endpoint
path on the same side of the bipartition, contradicting path parity. -/
theorem source_external_species_eq_of_reachable
    {anchor target : IndexedMatching Q} {x y : X}
    (hxy : (anchor.subgraph.spanningCoe ∆ target.subgraph.spanningCoe).Reachable
      (Sum.inl x) (Sum.inl y))
    (hxext : x ∉ anchor.species) (hyext : y ∉ anchor.species) :
    x = y := by
  classical
  by_contra hne
  obtain ⟨p, hp⟩ := hxy.exists_isPath
  have hpnon : ¬p.Nil := by
    intro hnil
    exact hne (Sum.inl.inj (hnil.eq))
  have hopposite := SimpleGraph.exchangePath_has_external_opposite_endpoints
    anchor.subgraph_isMatching target.subgraph_isMatching
    (reactantGraph_isBipartite Q) p hp hpnon hxext hyext
  simp at hopposite

omit [Fintype X] [Fintype R] in
theorem source_external_reaction_eq_of_reachable
    {anchor target : IndexedMatching Q} {r s : R}
    (hrs : (anchor.subgraph.spanningCoe ∆ target.subgraph.spanningCoe).Reachable
      (Sum.inr r) (Sum.inr s))
    (hrext : r ∉ anchor.reactions) (hsext : s ∉ anchor.reactions) :
    r = s := by
  classical
  by_contra hne
  obtain ⟨p, hp⟩ := hrs.exists_isPath
  have hpnon : ¬p.Nil := by
    intro hnil
    exact hne (Sum.inr.inj hnil.eq)
  have hopposite := SimpleGraph.exchangePath_has_external_opposite_endpoints
    anchor.subgraph_isMatching target.subgraph_isMatching
    (reactantGraph_isBipartite Q) p hp hpnon hrext hsext
  simp at hopposite

/-- A list represents one complete external-endpoint component of the target
exchange graph. -/
def RepresentsTargetExchangePath (anchor target : IndexedMatching Q)
    (path : List (X ⊕ R)) : Prop :=
  ∃ x r,
    x ∉ anchor.species ∧ r ∉ anchor.reactions ∧
      ∃ p : (anchor.subgraph.spanningCoe ∆ target.subgraph.spanningCoe).Walk
        (Sum.inl x) (Sum.inr r), p.IsPath ∧ p.support = path

/-- The proof witness pack is obtained by retaining, in executable DFS order,
exactly those emitted paths that are genuine target exchange components.  It
is used only in the completeness proof; the enumerator itself does not know
the target. -/
noncomputable def sourceTargetExchangePack
    (anchor target : IndexedMatching Q)
    (speciesOrder : List X) (reactionOrder : List R) :
    List (List (X ⊕ R)) := by
  classical
  exact (directBoundaryPaths (sourceExchangeNext Q anchor reactionOrder)
    (sourceBoundaryTarget anchor) (sourceBoundaryStarts anchor speciesOrder)).filter
      fun path => decide (RepresentsTargetExchangePath anchor target path)

theorem mem_sourceTargetExchangePack_iff
    (anchor target : IndexedMatching Q)
    (speciesOrder : List X) (reactionOrder : List R) (path : List (X ⊕ R)) :
    path ∈ sourceTargetExchangePack anchor target speciesOrder reactionOrder ↔
      path ∈ directBoundaryPaths (sourceExchangeNext Q anchor reactionOrder)
        (sourceBoundaryTarget anchor) (sourceBoundaryStarts anchor speciesOrder) ∧
      RepresentsTargetExchangePath anchor target path := by
  classical
  simp [sourceTargetExchangePack]

/-- Distinct target-component paths selected in DFS order are vertex-disjoint. -/
theorem sourceTargetExchangePack_pairwise_disjoint
    {anchor target : IndexedMatching Q}
    (hunique : SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (hcontains : anchor.VertexContained target)
    (speciesOrder : List X) (reactionOrder : List R) :
    (sourceTargetExchangePack anchor target speciesOrder reactionOrder).Pairwise
      fun p q => Disjoint p.toFinset q.toFinset := by
  classical
  let paths := directBoundaryPaths (sourceExchangeNext Q anchor reactionOrder)
    (sourceBoundaryTarget anchor) (sourceBoundaryStarts anchor speciesOrder)
  let pack := sourceTargetExchangePack anchor target speciesOrder reactionOrder
  have hprofile := source_exchange_profile hunique hcontains
  have hnodupPaths : paths.Nodup :=
    nodup_directBoundaryPaths _ _ _
      (sourceBoundaryStarts_nodup anchor speciesOrder)
      (sourceExchangeNext_nodup Q anchor reactionOrder)
  have hnodup : pack.Nodup := by
    exact hnodupPaths.sublist
      (show pack.Sublist paths from List.filter_sublist)
  have hoverlap : ∀ a ∈ pack, ∀ b ∈ pack,
      (∃ z, z ∈ a.toFinset ∧ z ∈ b.toFinset) → a = b := by
    intro a ha b hb hover
    have harep := (mem_sourceTargetExchangePack_iff
      anchor target speciesOrder reactionOrder a).1 ha |>.2
    have hbrep := (mem_sourceTargetExchangePack_iff
      anchor target speciesOrder reactionOrder b).1 hb |>.2
    rcases harep with ⟨x, r, hx, hr, p, hp, rfl⟩
    rcases hbrep with ⟨y, s, hy, hs, q, hq, rfl⟩
    obtain ⟨z, hzp, hzq⟩ := hover
    have hzp' : z ∈ p.support := by simpa using hzp
    have hzq' : z ∈ q.support := by simpa using hzq
    have hxyReach := (p.takeUntil z hzp').reachable.trans
      (q.takeUntil z hzq').reachable.symm
    have hxy : x = y :=
      source_external_species_eq_of_reachable hxyReach hx hy
    subst y
    have hrsReach := p.reachable.symm.trans q.reachable
    have hrs : r = s :=
      source_external_reaction_eq_of_reachable hrsReach hr hs
    subst s
    have hpq : (⟨p, hp⟩ :
        (anchor.subgraph.spanningCoe ∆ target.subgraph.spanningCoe).Path
          (Sum.inl x) (Sum.inr r)) = ⟨q, hq⟩ :=
      hprofile.1.1.path_unique _ _
    exact congrArg (fun z => z.val.support) hpq
  change pack.Pairwise fun p q => Disjoint p.toFinset q.toFinset
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [Finset.disjoint_left]
  intro z hzi hzj
  have heq := hoverlap pack[i] (by simp) pack[j] (by simp) ⟨z, hzi, hzj⟩
  have hfin : (⟨i, hi⟩ : Fin pack.length) = ⟨j, hj⟩ :=
    (List.nodup_iff_injective_getElem.mp hnodup) heq
  exact (Nat.ne_of_lt hij) (congrArg Fin.val hfin)

theorem sourceTargetExchangePack_paths_nodup
    (anchor target : IndexedMatching Q)
    (speciesOrder : List X) (reactionOrder : List R) :
    ∀ path ∈ sourceTargetExchangePack anchor target speciesOrder reactionOrder,
      path.Nodup := by
  intro path hpath
  have hrep := (mem_sourceTargetExchangePack_iff anchor target speciesOrder
    reactionOrder path).1 hpath |>.2
  rcases hrep with ⟨x, r, hx, hr, p, hp, rfl⟩
  exact hp.support_nodup

theorem sourceTargetExchangePack_forward_fst_nodup
    {anchor target : IndexedMatching Q}
    (hunique : SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (hcontains : anchor.VertexContained target)
    (speciesOrder : List X) (reactionOrder : List R) :
    (forwardPackEdges (sourceTargetExchangePack anchor target
      speciesOrder reactionOrder) |>.map Prod.fst).Nodup := by
  let pack := sourceTargetExchangePack anchor target speciesOrder reactionOrder
  have h := nodup_flatMap_of_map_sublist pack
    (fun path => (forwardEdges path).map Prod.fst) Sum.inl
    (sourceTargetExchangePack_paths_nodup anchor target speciesOrder reactionOrder)
    (sourceTargetExchangePack_pairwise_disjoint hunique hcontains
      speciesOrder reactionOrder)
    (by
      intro path
      simpa [List.map_map, Function.comp_def] using
        (map_inl_fst_forwardEdges_sublist path))
  rw [forwardPackEdges, List.map_flatMap]
  simpa [pack] using h

theorem sourceTargetExchangePack_forward_snd_nodup
    {anchor target : IndexedMatching Q}
    (hunique : SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (hcontains : anchor.VertexContained target)
    (speciesOrder : List X) (reactionOrder : List R) :
    (forwardPackEdges (sourceTargetExchangePack anchor target
      speciesOrder reactionOrder) |>.map Prod.snd).Nodup := by
  let pack := sourceTargetExchangePack anchor target speciesOrder reactionOrder
  have h := nodup_flatMap_of_map_sublist pack
    (fun path => (forwardEdges path).map Prod.snd) Sum.inr
    (sourceTargetExchangePack_paths_nodup anchor target speciesOrder reactionOrder)
    (sourceTargetExchangePack_pairwise_disjoint hunique hcontains
      speciesOrder reactionOrder)
    (by
      intro path
      simpa [List.map_map, Function.comp_def] using
        (map_inr_snd_forwardEdges_sublist path))
  rw [forwardPackEdges, List.map_flatMap]
  simpa [pack] using h

theorem sourceTargetExchangePack_mem_sourcePathPacks
    {anchor target : IndexedMatching Q}
    (hunique : SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (hcontains : anchor.VertexContained target)
    (speciesOrder : List X) (reactionOrder : List R) :
    sourceTargetExchangePack anchor target speciesOrder reactionOrder ∈
      sourcePathPacks Q anchor speciesOrder reactionOrder := by
  rw [sourcePathPacks, mem_directBoundaryPathPacks_iff]
  exact ⟨List.filter_sublist,
    sourceTargetExchangePack_pairwise_disjoint hunique hcontains
      speciesOrder reactionOrder⟩

theorem sourceTargetExchangePack_path_oriented
    {anchor target : IndexedMatching Q}
    (hunique : SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (hcontains : anchor.VertexContained target)
    (speciesOrder : List X) (reactionOrder : List R)
    {path : List (X ⊕ R)}
    (hpath : path ∈ sourceTargetExchangePack anchor target
      speciesOrder reactionOrder) :
    SourceOriented anchor.subgraph.spanningCoe path := by
  have hrep := (mem_sourceTargetExchangePack_iff anchor target speciesOrder
    reactionOrder path).1 hpath |>.2
  rcases hrep with ⟨x, r, hx, hr, p, hp, rfl⟩
  exact source_exchange_path_sourceOriented hunique hcontains hx p hp

/-- Every symmetric-difference edge is covered by one of the target component
paths retained by the source-level DFS enumeration. -/
theorem sourceTargetExchangePack_covers_exchange_adj
    {anchor target : IndexedMatching Q}
    (hunique : SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (hcontains : anchor.VertexContained target)
    (speciesOrder : List X) (hspecies : ∀ x, x ∈ speciesOrder)
    (reactionOrder : List R) (hreactions : ∀ r, r ∈ reactionOrder)
    {a b : X ⊕ R}
    (hab : (anchor.subgraph.spanningCoe ∆ target.subgraph.spanningCoe).Adj a b) :
    ∃ path ∈ sourceTargetExchangePack anchor target speciesOrder reactionOrder,
      ∃ x r, ∃ p :
        (anchor.subgraph.spanningCoe ∆ target.subgraph.spanningCoe).Walk
          (Sum.inl x) (Sum.inr r),
        p.support = path ∧ p.toSubgraph.Adj a b := by
  classical
  have hprofile := source_exchange_profile hunique hcontains
  obtain ⟨x, r, p, hx, hr, hp, hcover⟩ :=
    hprofile.exists_path_covering_adj hab
  have hpath : p.support ∈ directBoundaryPaths
      (sourceExchangeNext Q anchor reactionOrder)
      (sourceBoundaryTarget anchor)
      (sourceBoundaryStarts anchor speciesOrder) :=
    source_exchange_path_mem_directBoundaryPaths hunique hcontains
      speciesOrder hspecies reactionOrder hreactions hx hr p hp
  have hrep : RepresentsTargetExchangePath anchor target p.support :=
    ⟨x, r, hx, hr, p, hp, rfl⟩
  refine ⟨p.support, ?_, x, r, p, rfl, hcover⟩
  exact (mem_sourceTargetExchangePack_iff anchor target speciesOrder
    reactionOrder p.support).2 ⟨hpath, hrep⟩

/-- The executable forward-edge table is exactly the target-only half of the
symmetric difference. -/
theorem mem_forwardPackEdges_sourceTargetExchangePack_iff
    {anchor target : IndexedMatching Q}
    (hunique : SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (hcontains : anchor.VertexContained target)
    (speciesOrder : List X) (hspecies : ∀ x, x ∈ speciesOrder)
    (reactionOrder : List R) (hreactions : ∀ r, r ∈ reactionOrder)
    (e : X × R) :
    e ∈ forwardPackEdges (sourceTargetExchangePack anchor target
      speciesOrder reactionOrder) ↔
      target.subgraph.Adj (Sum.inl e.1) (Sum.inr e.2) ∧
        ¬anchor.subgraph.Adj (Sum.inl e.1) (Sum.inr e.2) := by
  classical
  rw [forwardPackEdges, List.mem_flatMap]
  constructor
  · rintro ⟨path, hpath, he⟩
    have horient := sourceTargetExchangePack_path_oriented hunique hcontains
      speciesOrder reactionOrder hpath
    have hrep := (mem_sourceTargetExchangePack_iff anchor target speciesOrder
      reactionOrder path).1 hpath |>.2
    rcases hrep with ⟨x, r, hx, hr, p, hp, hsupport⟩
    have he' : e ∈ forwardEdges p.support := hsupport ▸ he
    have hedge : s(Sum.inl e.1, Sum.inr e.2) ∈ p.edges :=
      (mem_walk_edges_iff_forward_or_backward p e.1 e.2).2 (Or.inl he')
    have hP : (anchor.subgraph.spanningCoe ∆
        target.subgraph.spanningCoe).Adj
        (Sum.inl e.1) (Sum.inr e.2) :=
      p.toSubgraph.adj_sub
        (_root_.SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr hedge)
    have hnotA : ¬anchor.subgraph.Adj
        (Sum.inl e.1) (Sum.inr e.2) := horient.1 e he
    simp only [symmDiff_def, _root_.SimpleGraph.sup_adj,
      _root_.SimpleGraph.sdiff_adj, Subgraph.spanningCoe_adj] at hP
    rcases hP with hP | hP
    · exact (hnotA hP.1).elim
    · exact ⟨hP.1, hnotA⟩
  · rintro ⟨hT, hnotA⟩
    have hP : (anchor.subgraph.spanningCoe ∆
        target.subgraph.spanningCoe).Adj
        (Sum.inl e.1) (Sum.inr e.2) := by
      simp [symmDiff_def, hT, hnotA]
    obtain ⟨path, hpath, x, r, p, hsupport, hcover⟩ :=
      sourceTargetExchangePack_covers_exchange_adj hunique hcontains
        speciesOrder hspecies reactionOrder hreactions hP
    have hedge : s(Sum.inl e.1, Sum.inr e.2) ∈ p.edges :=
      _root_.SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp hcover
    have horient := sourceTargetExchangePack_path_oriented hunique hcontains
      speciesOrder reactionOrder hpath
    have horient' : SourceOriented anchor.subgraph.spanningCoe p.support :=
      hsupport ▸ horient
    rcases (mem_walk_edges_iff_forward_or_backward p e.1 e.2).1 hedge with
      he | he
    · exact ⟨path, hpath, hsupport ▸ he⟩
    · exact (hnotA (horient'.2 e he)).elim

/-- The executable backward-edge table is exactly the anchor-only half of the
symmetric difference. -/
theorem mem_backwardPackEdges_sourceTargetExchangePack_iff
    {anchor target : IndexedMatching Q}
    (hunique : SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (hcontains : anchor.VertexContained target)
    (speciesOrder : List X) (hspecies : ∀ x, x ∈ speciesOrder)
    (reactionOrder : List R) (hreactions : ∀ r, r ∈ reactionOrder)
    (e : X × R) :
    e ∈ backwardPackEdges (sourceTargetExchangePack anchor target
      speciesOrder reactionOrder) ↔
      anchor.subgraph.Adj (Sum.inl e.1) (Sum.inr e.2) ∧
        ¬target.subgraph.Adj (Sum.inl e.1) (Sum.inr e.2) := by
  classical
  rw [backwardPackEdges, List.mem_flatMap]
  constructor
  · rintro ⟨path, hpath, he⟩
    have horient := sourceTargetExchangePack_path_oriented hunique hcontains
      speciesOrder reactionOrder hpath
    have hrep := (mem_sourceTargetExchangePack_iff anchor target speciesOrder
      reactionOrder path).1 hpath |>.2
    rcases hrep with ⟨x, r, hx, hr, p, hp, hsupport⟩
    have he' : e ∈ backwardEdges p.support := hsupport ▸ he
    have hedge : s(Sum.inl e.1, Sum.inr e.2) ∈ p.edges :=
      (mem_walk_edges_iff_forward_or_backward p e.1 e.2).2 (Or.inr he')
    have hP : (anchor.subgraph.spanningCoe ∆
        target.subgraph.spanningCoe).Adj
        (Sum.inl e.1) (Sum.inr e.2) :=
      p.toSubgraph.adj_sub
        (_root_.SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr hedge)
    have hA : anchor.subgraph.Adj
        (Sum.inl e.1) (Sum.inr e.2) := horient.2 e he
    simp only [symmDiff_def, _root_.SimpleGraph.sup_adj,
      _root_.SimpleGraph.sdiff_adj, Subgraph.spanningCoe_adj] at hP
    rcases hP with hP | hP
    · exact ⟨hA, hP.2⟩
    · exact (hP.2 hA).elim
  · rintro ⟨hA, hnotT⟩
    have hP : (anchor.subgraph.spanningCoe ∆
        target.subgraph.spanningCoe).Adj
        (Sum.inl e.1) (Sum.inr e.2) := by
      simp [symmDiff_def, hA, hnotT]
    obtain ⟨path, hpath, x, r, p, hsupport, hcover⟩ :=
      sourceTargetExchangePack_covers_exchange_adj hunique hcontains
        speciesOrder hspecies reactionOrder hreactions hP
    have hedge : s(Sum.inl e.1, Sum.inr e.2) ∈ p.edges :=
      _root_.SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp hcover
    have horient := sourceTargetExchangePack_path_oriented hunique hcontains
      speciesOrder reactionOrder hpath
    have horient' : SourceOriented anchor.subgraph.spanningCoe p.support :=
      hsupport ▸ horient
    rcases (mem_walk_edges_iff_forward_or_backward p e.1 e.2).1 hedge with
      he | he
    · exact (horient'.1 e he hA).elim
    · exact ⟨path, hpath, hsupport ▸ he⟩

/-- Toggling the canonical target component pack reconstructs exactly the
target edge relation (independently of the target's `Fin` indexing order). -/
theorem mem_toggledEdges_sourceTargetExchangePack_iff
    {anchor target : IndexedMatching Q}
    (hunique : SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (hcontains : anchor.VertexContained target)
    (speciesOrder : List X) (hspecies : ∀ x, x ∈ speciesOrder)
    (reactionOrder : List R) (hreactions : ∀ r, r ∈ reactionOrder)
    (e : X × R) :
    e ∈ toggledEdges anchor (sourceTargetExchangePack anchor target
      speciesOrder reactionOrder) ↔ e ∈ target.edgeList := by
  classical
  have hAiff : anchor.subgraph.Adj (Sum.inl e.1) (Sum.inr e.2) ↔
      e ∈ anchor.edgeList := by
    rw [IndexedMatching.mem_edgeList_iff]
    rfl
  have hTiff : target.subgraph.Adj (Sum.inl e.1) (Sum.inr e.2) ↔
      e ∈ target.edgeList := by
    rw [IndexedMatching.mem_edgeList_iff]
    rfl
  rw [toggledEdges, List.mem_append, List.mem_filter,
    mem_forwardPackEdges_sourceTargetExchangePack_iff hunique hcontains
      speciesOrder hspecies reactionOrder hreactions e]
  simp only [decide_eq_true_eq]
  rw [
    mem_backwardPackEdges_sourceTargetExchangePack_iff hunique hcontains
      speciesOrder hspecies reactionOrder hreactions e,
    ← hAiff, ← hTiff]
  by_cases hA : e ∈ anchor.edgeList <;> simp_all

theorem toggledEdges_sourceTargetExchangePack_nodup
    {anchor target : IndexedMatching Q}
    (hunique : SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (hcontains : anchor.VertexContained target)
    (speciesOrder : List X) (hspecies : ∀ x, x ∈ speciesOrder)
    (reactionOrder : List R) (hreactions : ∀ r, r ∈ reactionOrder) :
    (toggledEdges anchor (sourceTargetExchangePack anchor target
      speciesOrder reactionOrder)).Nodup := by
  classical
  let pack := sourceTargetExchangePack anchor target speciesOrder reactionOrder
  have hanchor :
      (anchor.edgeList.filter (fun e => e ∉ backwardPackEdges pack)).Nodup :=
    anchor.edgeList_nodup.filter _
  have hforwardMap : (forwardPackEdges pack |>.map Prod.fst).Nodup := by
    simpa [pack] using sourceTargetExchangePack_forward_fst_nodup
      hunique hcontains speciesOrder reactionOrder
  have hforward : (forwardPackEdges pack).Nodup :=
    List.Nodup.of_map Prod.fst hforwardMap
  have hdisjoint : List.Disjoint
      (anchor.edgeList.filter (fun e => e ∉ backwardPackEdges pack))
      (forwardPackEdges pack) := by
    rw [List.disjoint_left]
    intro e heanchor heforward
    have heAList : e ∈ anchor.edgeList := (List.mem_filter.mp heanchor).1
    have heA : anchor.subgraph.Adj (Sum.inl e.1) (Sum.inr e.2) := by
      rw [IndexedMatching.mem_edgeList_iff] at heAList
      exact heAList
    have heforward' :=
      (mem_forwardPackEdges_sourceTargetExchangePack_iff hunique hcontains
        speciesOrder hspecies reactionOrder hreactions e).1
        (by simpa [pack] using heforward)
    exact heforward'.2 heA
  rw [toggledEdges]
  exact hanchor.append hforward hdisjoint

/-- The target component pack passes the source constructor's exact matching
and reactant-incidence validator. -/
theorem matchingEdgesOK_sourceTargetExchangePack
    {anchor target : IndexedMatching Q}
    (hunique : SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (hcontains : anchor.VertexContained target)
    (speciesOrder : List X) (hspecies : ∀ x, x ∈ speciesOrder)
    (reactionOrder : List R) (hreactions : ∀ r, r ∈ reactionOrder) :
    MatchingEdgesOK Q (toggledEdges anchor
      (sourceTargetExchangePack anchor target speciesOrder reactionOrder)) := by
  classical
  let edges := toggledEdges anchor
    (sourceTargetExchangePack anchor target speciesOrder reactionOrder)
  have hedges : edges.Nodup := by
    simpa [edges] using toggledEdges_sourceTargetExchangePack_nodup
      hunique hcontains speciesOrder hspecies reactionOrder hreactions
  have hmem (e : X × R) : e ∈ edges ↔ e ∈ target.edgeList := by
    simpa [edges] using mem_toggledEdges_sourceTargetExchangePack_iff
      hunique hcontains speciesOrder hspecies reactionOrder hreactions e
  refine ⟨hedges.map_on ?_, hedges.map_on ?_, ?_⟩
  · intro e he f hf hef
    rcases (IndexedMatching.mem_edgeList_iff target e.1 e.2).1
      (hmem e |>.1 he) with ⟨i, hix, hir⟩
    rcases (IndexedMatching.mem_edgeList_iff target f.1 f.2).1
      (hmem f |>.1 hf) with ⟨j, hjx, hjr⟩
    have hij : i = j := target.left_injective (hix.trans (hef.trans hjx.symm))
    subst j
    exact Prod.ext hef (hir.symm.trans hjr)
  · intro e he f hf hef
    rcases (IndexedMatching.mem_edgeList_iff target e.1 e.2).1
      (hmem e |>.1 he) with ⟨i, hix, hir⟩
    rcases (IndexedMatching.mem_edgeList_iff target f.1 f.2).1
      (hmem f |>.1 hf) with ⟨j, hjx, hjr⟩
    have hij : i = j := target.right_injective (hir.trans (hef.trans hjr.symm))
    subst j
    exact Prod.ext (hix.symm.trans hjx) hef
  · intro e he
    rcases (IndexedMatching.mem_edgeList_iff target e.1 e.2).1
      (hmem e |>.1 he) with ⟨i, hix, hir⟩
    rw [← hix, ← hir]
    exact target.reactant_edge i

theorem buildPathPackCandidate_sourceTargetExchangePack_isSome
    {anchor target : IndexedMatching Q}
    (hunique : SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (hcontains : anchor.VertexContained target)
    (speciesOrder : List X) (hspecies : ∀ x, x ∈ speciesOrder)
    (reactionOrder : List R) (hreactions : ∀ r, r ∈ reactionOrder) :
    (buildPathPackCandidate? Q anchor
      (sourceTargetExchangePack anchor target speciesOrder reactionOrder)).isSome := by
  rw [buildPathPackCandidate_isSome_iff]
  exact matchingEdgesOK_sourceTargetExchangePack hunique hcontains
    speciesOrder hspecies reactionOrder hreactions

/-- Completeness in the extensional output representation: the direct
source-level DFS emits the target matching's edge set, regardless of the
target's private `Fin` indexing order. -/
theorem target_edgeFinset_mem_sourceCandidateEdgeFinsets
    {anchor target : IndexedMatching Q}
    (hunique : SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph)
    (hcontains : anchor.VertexContained target)
    (speciesOrder : List X) (hspecies : ∀ x, x ∈ speciesOrder)
    (reactionOrder : List R) (hreactions : ∀ r, r ∈ reactionOrder) :
    target.edgeFinset ∈ sourceCandidateEdgeFinsets Q anchor
      speciesOrder reactionOrder := by
  classical
  let pack := sourceTargetExchangePack anchor target speciesOrder reactionOrder
  have hok : MatchingEdgesOK Q (toggledEdges anchor pack) := by
    simpa [pack] using matchingEdgesOK_sourceTargetExchangePack
      hunique hcontains speciesOrder hspecies reactionOrder hreactions
  have hvalid : matchingEdgesValid Q (toggledEdges anchor pack) = true :=
    (matchingEdgesValid_eq_true_iff Q _).2 hok
  let candidate := IndexedMatching.ofValidEdges Q (toggledEdges anchor pack) hvalid
  have hcandidate : buildPathPackCandidate? Q anchor pack = some candidate := by
    simp [buildPathPackCandidate?, hvalid, candidate]
  have hpack : pack ∈ sourcePathPacks Q anchor speciesOrder reactionOrder := by
    simpa [pack] using sourceTargetExchangePack_mem_sourcePathPacks
      hunique hcontains speciesOrder reactionOrder
  have hcandidateMem : candidate ∈
      sourceCandidates Q anchor speciesOrder reactionOrder :=
    (mem_sourceCandidates_iff Q anchor candidate speciesOrder reactionOrder).2
      ⟨pack, hpack, hcandidate⟩
  have hedgeFinset : candidate.edgeFinset = target.edgeFinset := by
    ext e
    rw [IndexedMatching.edgeFinset, IndexedMatching.edgeFinset]
    simp only [List.mem_toFinset]
    rw [edgeList_of_buildPathPackCandidate Q anchor candidate pack hcandidate]
    exact mem_toggledEdges_sourceTargetExchangePack_iff hunique hcontains
      speciesOrder hspecies reactionOrder hreactions e
  rw [sourceCandidateEdgeFinsets, List.mem_map]
  exact ⟨candidate, hcandidateMem, hedgeFinset⟩

end AutocatalyticCS
