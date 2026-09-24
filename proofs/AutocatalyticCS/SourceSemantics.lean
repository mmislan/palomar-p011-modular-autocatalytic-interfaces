import proofs.AutocatalyticCS.DirectPathPack
import proofs.AutocatalyticCS.Basic
import Mathlib.Logic.Equiv.Fintype

/-!
A source-faithful, executable representation of a child selection by an
indexed table of matching edges. Injectivity of both endpoint arrays is
exactly the matching invariant; positivity is checked against the input
reaction network.
-/

namespace AutocatalyticCS

variable {X R : Type*} [DecidableEq X] [DecidableEq R]
variable {Q : ReactionNetwork X R}

structure IndexedMatching (Q : ReactionNetwork X R) where
  card : Nat
  left : Fin card → X
  right : Fin card → R
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  reactant_edge : ∀ i, 0 < Q.reactant (left i) (right i)

namespace IndexedMatching

def species (E : IndexedMatching Q) : Finset X :=
  Finset.univ.image E.left

def reactions (E : IndexedMatching Q) : Finset R :=
  Finset.univ.image E.right

private def leftEmbedding (E : IndexedMatching Q) : Fin E.card ↪ X :=
  ⟨E.left, E.left_injective⟩

private def rightEmbedding (E : IndexedMatching Q) : Fin E.card ↪ R :=
  ⟨E.right, E.right_injective⟩

private def leftRangeEquiv (E : IndexedMatching Q) :
    {x // x ∈ Set.range E.left} ≃ {x // x ∈ E.species} :=
  Equiv.subtypeEquivRight fun x => by simp [species]

private def rightRangeEquiv (E : IndexedMatching Q) :
    {r // r ∈ Set.range E.right} ≃ {r // r ∈ E.reactions} :=
  Equiv.subtypeEquivRight fun r => by simp [reactions]

private def leftIndexEquiv (E : IndexedMatching Q) :
    {x // x ∈ E.species} ≃ Fin E.card :=
  E.leftRangeEquiv.symm |>.trans E.leftEmbedding.toEquivRange.symm

private def rightIndexEquiv (E : IndexedMatching Q) :
    {r // r ∈ E.reactions} ≃ Fin E.card :=
  E.rightRangeEquiv.symm |>.trans E.rightEmbedding.toEquivRange.symm

def assign (E : IndexedMatching Q) :
    {x // x ∈ E.species} ≃ {r // r ∈ E.reactions} :=
  E.leftIndexEquiv |>.trans E.rightIndexEquiv.symm

omit [DecidableEq R] in
private theorem leftIndex_symm_val (E : IndexedMatching Q) (i : Fin E.card) :
    ((E.leftIndexEquiv).symm i).1 = E.left i := by
  change (E.leftEmbedding.toEquivRange i).1 = E.left i
  rfl

omit [DecidableEq X] in
private theorem rightIndex_symm_val (E : IndexedMatching Q) (i : Fin E.card) :
    ((E.rightIndexEquiv).symm i).1 = E.right i := by
  change (E.rightEmbedding.toEquivRange i).1 = E.right i
  rfl

theorem assign_index (E : IndexedMatching Q) (i : Fin E.card) :
    (E.assign ((E.leftIndexEquiv).symm i)).1 = E.right i := by
  simp [assign, E.rightIndex_symm_val]

def toChildSelection (E : IndexedMatching Q) : ChildSelection Q where
  species := E.species
  reactions := E.reactions
  assign := E.assign
  reactant_match := by
    intro x
    let i := E.leftIndexEquiv x
    have hleft : x.1 = E.left i := by
      simpa [i] using E.leftIndex_symm_val i
    have hright : (E.assign x).1 = E.right i := by
      simpa [i] using E.assign_index i
    simpa [hleft, hright] using E.reactant_edge i

theorem toChildSelection_species (E : IndexedMatching Q) :
    E.toChildSelection.species = E.species := rfl

theorem toChildSelection_reactions (E : IndexedMatching Q) :
    E.toChildSelection.reactions = E.reactions := rfl

theorem toChildSelection_assign_index (E : IndexedMatching Q) (i : Fin E.card) :
    (E.toChildSelection.assign ((E.leftIndexEquiv).symm i)).1 = E.right i :=
  E.assign_index i

theorem exists_index_of_species (E : IndexedMatching Q) (x : E.species) :
    ∃ i : Fin E.card,
      E.left i = x.1 ∧ E.right i = (E.assign x).1 := by
  let i := E.leftIndexEquiv x
  refine ⟨i, ?_, ?_⟩
  · simpa [i] using (E.leftIndex_symm_val i).symm
  · simpa [i] using (E.assign_index i).symm

theorem toChildSelection_matrix (E : IndexedMatching Q)
    (x y : E.toChildSelection.species) :
    E.toChildSelection.matrix x y =
      Q.net x.1 (E.assign y).1 := rfl

theorem toChildSelection_autocatalytic_iff (E : IndexedMatching Q) :
    E.toChildSelection.Autocatalytic ↔
      Semipositive (fun i j => (Q.net i.1 (E.assign j).1 : ℚ)) := by
  rfl

end IndexedMatching

/-- Concrete matching and source-incidence conditions for an ordered edge
table.  This proposition is decidable on the finite index type. -/
def MatchingEdgesOK (Q : ReactionNetwork X R) (edges : List (X × R)) : Prop :=
  (edges.map Prod.fst).Nodup ∧
  (edges.map Prod.snd).Nodup ∧
  ∀ e ∈ edges, 0 < Q.reactant e.1 e.2

def matchingEdgesValid (Q : ReactionNetwork X R) (edges : List (X × R)) : Bool :=
  decide (edges.map Prod.fst).Nodup &&
    decide (edges.map Prod.snd).Nodup &&
    edges.all fun e => decide (0 < Q.reactant e.1 e.2)

theorem matchingEdgesValid_eq_true_iff (Q : ReactionNetwork X R)
    (edges : List (X × R)) :
    matchingEdgesValid Q edges = true ↔ MatchingEdgesOK Q edges := by
  simp [matchingEdgesValid, MatchingEdgesOK, and_assoc]

def IndexedMatching.ofValidEdges (Q : ReactionNetwork X R) (edges : List (X × R))
    (h : matchingEdgesValid Q edges = true) : IndexedMatching Q := by
  have hok := (matchingEdgesValid_eq_true_iff Q edges).1 h
  exact
    { card := edges.length
      left := fun i => (edges.get i).1
      right := fun i => (edges.get i).2
      left_injective := by
        intro i j hij
        let i' : Fin (edges.map Prod.fst).length := ⟨i, by simp⟩
        let j' : Fin (edges.map Prod.fst).length := ⟨j, by simp⟩
        have heq : i' = j' := hok.1.get_inj_iff.mp (by simpa [i', j'] using hij)
        have hv : i'.val = j'.val := congrArg (fun z => z.val) heq
        exact Fin.ext (show i.val = j.val from hv)
      right_injective := by
        intro i j hij
        let i' : Fin (edges.map Prod.snd).length := ⟨i, by simp⟩
        let j' : Fin (edges.map Prod.snd).length := ⟨j, by simp⟩
        have heq : i' = j' := hok.2.1.get_inj_iff.mp (by simpa [i', j'] using hij)
        have hv : i'.val = j'.val := congrArg (fun z => z.val) heq
        exact Fin.ext (show i.val = j.val from hv)
      reactant_edge := fun i => hok.2.2 (edges.get i) (edges.get_mem i) }

def IndexedMatching.edgeList (E : IndexedMatching Q) : List (X × R) :=
  List.ofFn fun i => (E.left i, E.right i)

def IndexedMatching.edgeFinset (E : IndexedMatching Q) : Finset (X × R) :=
  E.edgeList.toFinset

omit [DecidableEq X] [DecidableEq R] in
theorem IndexedMatching.edgeList_nodup (E : IndexedMatching Q) :
    E.edgeList.Nodup := by
  rw [IndexedMatching.edgeList, List.nodup_ofFn]
  intro i j hij
  exact E.left_injective (congrArg Prod.fst hij)

theorem IndexedMatching.edgeList_ofValidEdges (Q : ReactionNetwork X R)
    (edges : List (X × R)) (h : matchingEdgesValid Q edges = true) :
    (IndexedMatching.ofValidEdges Q edges h).edgeList = edges := by
  apply List.ext_get
  · simp [IndexedMatching.edgeList, IndexedMatching.ofValidEdges]
  · intro n h₁ h₂
    simp [IndexedMatching.edgeList, IndexedMatching.ofValidEdges]

omit [DecidableEq X] [DecidableEq R] in
theorem IndexedMatching.mem_edgeList_iff (E : IndexedMatching Q) (x : X) (r : R) :
    (x, r) ∈ E.edgeList ↔ ∃ i : Fin E.card, E.left i = x ∧ E.right i = r := by
  simp [IndexedMatching.edgeList, List.mem_ofFn]

theorem IndexedMatching.assign_mem_edgeFinset
    (E : IndexedMatching Q) (x : E.species) :
    (x.1, (E.assign x).1) ∈ E.edgeFinset := by
  rcases E.exists_index_of_species x with ⟨i, hleft, hright⟩
  rw [IndexedMatching.edgeFinset, List.mem_toFinset,
    IndexedMatching.mem_edgeList_iff]
  exact ⟨i, hleft, hright⟩

/-- Non-anchor (species-to-reaction) edges encountered along a directed
alternating path. -/
def forwardEdges : List (X ⊕ R) → List (X × R)
  | Sum.inl x :: Sum.inr r :: tail => (x, r) :: forwardEdges (Sum.inr r :: tail)
  | _ :: tail => forwardEdges tail
  | [] => []

/-- Anchor (reaction-to-species) edges removed by an alternating path. -/
def backwardEdges : List (X ⊕ R) → List (X × R)
  | Sum.inr r :: Sum.inl x :: tail => (x, r) :: backwardEdges (Sum.inl x :: tail)
  | _ :: tail => backwardEdges tail
  | [] => []

omit [DecidableEq X] [DecidableEq R] in
/-- The two oriented edge lists record exactly the species--reaction edges of
a walk, forgetting only their traversal orientation. -/
theorem mem_walk_edges_iff_forward_or_backward
    {G : _root_.SimpleGraph (X ⊕ R)} {u v : X ⊕ R}
    (p : G.Walk u v) (x : X) (r : R) :
    s(Sum.inl x, Sum.inr r) ∈ p.edges ↔
      (x, r) ∈ forwardEdges p.support ∨
        (x, r) ∈ backwardEdges p.support := by
  induction p with
  | nil => simp [forwardEdges, backwardEdges]
  | @cons a b c hab q ih =>
      cases a <;> cases b <;> cases q <;>
        simp_all [forwardEdges, backwardEdges] <;> aesop

/-- Every forward edge is outside the reference matching and every backward
edge belongs to it. -/
def SourceOriented (reference : _root_.SimpleGraph (X ⊕ R))
    (path : List (X ⊕ R)) : Prop :=
  (∀ e ∈ forwardEdges path,
      ¬reference.Adj (Sum.inl e.1) (Sum.inr e.2)) ∧
    (∀ e ∈ backwardEdges path,
      reference.Adj (Sum.inl e.1) (Sum.inr e.2))

omit [DecidableEq X] [DecidableEq R] in
theorem map_inl_fst_forwardEdges_sublist (path : List (X ⊕ R)) :
    ((forwardEdges path).map (fun e => Sum.inl e.1)).Sublist path := by
  induction path using List.twoStepInduction with
  | nil => simp [forwardEdges]
  | singleton a => simp [forwardEdges]
  | cons_cons a b rest ihrest ihtail =>
      cases a <;> cases b <;> simp_all [forwardEdges]

omit [DecidableEq X] [DecidableEq R] in
theorem map_inl_fst_backwardEdges_sublist (path : List (X ⊕ R)) :
    ((backwardEdges path).map (fun e => Sum.inl e.1)).Sublist path := by
  induction path using List.twoStepInduction with
  | nil => simp [backwardEdges]
  | singleton a => simp [backwardEdges]
  | cons_cons a b rest ihrest ihtail =>
      cases a <;> cases b <;> simp_all [backwardEdges]

omit [DecidableEq X] [DecidableEq R] in
theorem map_inr_snd_forwardEdges_sublist (path : List (X ⊕ R)) :
    ((forwardEdges path).map (fun e => Sum.inr e.2)).Sublist path := by
  induction path using List.twoStepInduction with
  | nil => simp [forwardEdges]
  | singleton a => simp [forwardEdges]
  | cons_cons a b rest ihrest ihtail =>
      cases a <;> cases b <;> simp_all [forwardEdges]

omit [DecidableEq X] [DecidableEq R] in
theorem map_inr_snd_backwardEdges_sublist (path : List (X ⊕ R)) :
    ((backwardEdges path).map (fun e => Sum.inr e.2)).Sublist path := by
  induction path using List.twoStepInduction with
  | nil => simp [backwardEdges]
  | singleton a => simp [backwardEdges]
  | cons_cons a b rest ihrest ihtail =>
      cases a <;> cases b <;> simp_all [backwardEdges]

/-- A vertex-disjoint pack of simple paths cannot repeat any locally selected
vertex.  The selector is presented through an injective embedding whose image
is a sublist of the path; this form applies uniformly to both bipartition
projections of the oriented edge lists below. -/
theorem nodup_flatMap_of_map_sublist
    {A : Type*} (pack : List (List (X ⊕ R))) (select : List (X ⊕ R) → List A)
    (embed : A → X ⊕ R)
    (hpaths : ∀ path ∈ pack, path.Nodup)
    (hpair : pack.Pairwise fun p q => Disjoint p.toFinset q.toFinset)
    (hsub : ∀ path, (select path).map embed |>.Sublist path) :
    (pack.flatMap select).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro path hpath
    exact List.Nodup.of_map embed ((hpaths path hpath).sublist (hsub path))
  · rw [List.pairwise_iff_getElem] at hpair ⊢
    intro i j hi hj hij
    change List.Disjoint (select pack[i]) (select pack[j])
    rw [List.disjoint_left]
    intro a hai haj
    have hembedi : embed a ∈ pack[i] :=
      (hsub pack[i]).mem (List.mem_map_of_mem hai)
    have hembedj : embed a ∈ pack[j] :=
      (hsub pack[j]).mem (List.mem_map_of_mem haj)
    exact (Finset.disjoint_left.mp (hpair i j hi hj hij))
      (by simpa using hembedi) (by simpa using hembedj)

omit [DecidableEq X] [DecidableEq R] in
theorem SourceOriented.cons_walk
    {G reference : _root_.SimpleGraph (X ⊕ R)} {u w v : X ⊕ R}
    (huw : G.Adj u w) (q : G.Walk w v)
    (htail : SourceOriented reference q.support)
    (hforward : ∀ x r, u = Sum.inl x → w = Sum.inr r →
      ¬reference.Adj (Sum.inl x) (Sum.inr r))
    (hbackward : ∀ r x, u = Sum.inr r → w = Sum.inl x →
      reference.Adj (Sum.inl x) (Sum.inr r)) :
    SourceOriented reference ((_root_.SimpleGraph.Walk.cons huw q).support) := by
  rcases htail with ⟨hf, hb⟩
  cases u with
  | inl x =>
      cases w with
      | inl y =>
          have hfeq : forwardEdges ((_root_.SimpleGraph.Walk.cons huw q).support) =
              forwardEdges q.support := by cases q <;> rfl
          have hbeq : backwardEdges ((_root_.SimpleGraph.Walk.cons huw q).support) =
              backwardEdges q.support := by cases q <;> rfl
          rw [SourceOriented, hfeq, hbeq]
          exact ⟨hf, hb⟩
      | inr r =>
          have hfeq : forwardEdges ((_root_.SimpleGraph.Walk.cons huw q).support) =
              (x, r) :: forwardEdges q.support := by cases q <;> rfl
          have hbeq : backwardEdges ((_root_.SimpleGraph.Walk.cons huw q).support) =
              backwardEdges q.support := by cases q <;> rfl
          rw [SourceOriented, hfeq, hbeq]
          refine ⟨?_, hb⟩
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact hforward x r rfl rfl
          · exact hf e he
  | inr r =>
      cases w with
      | inl x =>
          have hfeq : forwardEdges ((_root_.SimpleGraph.Walk.cons huw q).support) =
              forwardEdges q.support := by cases q <;> rfl
          have hbeq : backwardEdges ((_root_.SimpleGraph.Walk.cons huw q).support) =
              (x, r) :: backwardEdges q.support := by cases q <;> rfl
          rw [SourceOriented, hfeq, hbeq]
          refine ⟨hf, ?_⟩
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact hbackward r x rfl rfl
          · exact hb e he
      | inr s =>
          have hfeq : forwardEdges ((_root_.SimpleGraph.Walk.cons huw q).support) =
              forwardEdges q.support := by cases q <;> rfl
          have hbeq : backwardEdges ((_root_.SimpleGraph.Walk.cons huw q).support) =
              backwardEdges q.support := by cases q <;> rfl
          rw [SourceOriented, hfeq, hbeq]
          exact ⟨hf, hb⟩

def forwardPackEdges (pack : List (List (X ⊕ R))) : List (X × R) :=
  pack.flatMap forwardEdges

def backwardPackEdges (pack : List (List (X ⊕ R))) : List (X × R) :=
  pack.flatMap backwardEdges

/-- Toggle an anchor edge table by the ordered alternating paths: delete every
backward (anchor) edge, then append every forward edge. -/
def toggledEdges (anchor : IndexedMatching Q) (pack : List (List (X ⊕ R))) :
    List (X × R) :=
  anchor.edgeList.filter (fun e => e ∉ backwardPackEdges pack) ++
    forwardPackEdges pack

/-- The executable source-level constructor.  Failed structural or reactant
checks reject the path pack; successful output carries the checked proof. -/
def buildPathPackCandidate? (Q : ReactionNetwork X R) (anchor : IndexedMatching Q)
    (pack : List (List (X ⊕ R))) : Option (IndexedMatching Q) :=
  if h : matchingEdgesValid Q (toggledEdges anchor pack) = true then
    some (IndexedMatching.ofValidEdges Q (toggledEdges anchor pack) h)
  else none

theorem buildPathPackCandidate_isSome_iff (Q : ReactionNetwork X R)
    (anchor : IndexedMatching Q) (pack : List (List (X ⊕ R))) :
    (buildPathPackCandidate? Q anchor pack).isSome ↔
      MatchingEdgesOK Q (toggledEdges anchor pack) := by
  rw [← matchingEdgesValid_eq_true_iff]
  simp [buildPathPackCandidate?]

theorem edgeList_of_buildPathPackCandidate (Q : ReactionNetwork X R)
    (anchor candidate : IndexedMatching Q) (pack : List (List (X ⊕ R)))
    (h : buildPathPackCandidate? Q anchor pack = some candidate) :
    candidate.edgeList = toggledEdges anchor pack := by
  simp only [buildPathPackCandidate?] at h
  split at h
  · rw [Option.some.inj h.symm]
    exact IndexedMatching.edgeList_ofValidEdges _ _ _
  · contradiction

section ConcreteSearch

/-- Source-derived alternating successors. Species point to every reaction in
which they occur as a reactant; reactions point backward along anchor edges.
`dedup` is local adjacency normalization, not output deduplication. -/
def sourceExchangeNext (Q : ReactionNetwork X R) (anchor : IndexedMatching Q)
    (reactionOrder : List R) :
    X ⊕ R → List (X ⊕ R)
  | Sum.inl x =>
      ((reactionOrder.filter fun r => 0 < Q.reactant x r).map Sum.inr).dedup
  | Sum.inr r =>
      (anchor.edgeList.filterMap fun e =>
        if e.2 = r then some (Sum.inl e.1) else none).dedup

def sourceBoundaryStarts (anchor : IndexedMatching Q) (speciesOrder : List X) :
    List (X ⊕ R) :=
  ((speciesOrder.filter fun x => x ∉ anchor.species).map Sum.inl).dedup

def sourceBoundaryTarget (anchor : IndexedMatching Q) : X ⊕ R → Bool
  | Sum.inl _ => false
  | Sum.inr r => decide (r ∉ anchor.reactions)

def sourcePathPacks [Fintype X] [Fintype R] (Q : ReactionNetwork X R)
    (anchor : IndexedMatching Q) (speciesOrder : List X) (reactionOrder : List R) :
    List (List (List (X ⊕ R))) :=
  directBoundaryPathPacks (sourceExchangeNext Q anchor reactionOrder)
    (sourceBoundaryTarget anchor) (sourceBoundaryStarts anchor speciesOrder)

def sourceCandidates [Fintype X] [Fintype R] (Q : ReactionNetwork X R)
    (anchor : IndexedMatching Q) (speciesOrder : List X) (reactionOrder : List R) :
    List (IndexedMatching Q) :=
  (sourcePathPacks Q anchor speciesOrder reactionOrder).filterMap
    (buildPathPackCandidate? Q anchor)

/-- Extensional output representation, independent of the internal `Fin`
ordering chosen when a path-pack candidate is built. -/
def sourceCandidateEdgeFinsets [Fintype X] [Fintype R]
    (Q : ReactionNetwork X R) (anchor : IndexedMatching Q)
    (speciesOrder : List X) (reactionOrder : List R) :
    List (Finset (X × R)) :=
  (sourceCandidates Q anchor speciesOrder reactionOrder).map
    IndexedMatching.edgeFinset

theorem sourceExchangeNext_nodup (Q : ReactionNetwork X R)
    (anchor : IndexedMatching Q) (reactionOrder : List R) (v : X ⊕ R) :
    (sourceExchangeNext Q anchor reactionOrder v).Nodup := by
  cases v <;> exact List.nodup_dedup _

theorem mem_sourceExchangeNext_inl_iff (Q : ReactionNetwork X R)
    (anchor : IndexedMatching Q) (reactionOrder : List R) (x : X) (r : R) :
    Sum.inr r ∈ sourceExchangeNext Q anchor reactionOrder (Sum.inl x) ↔
      r ∈ reactionOrder ∧ 0 < Q.reactant x r := by
  simp [sourceExchangeNext]

theorem mem_sourceExchangeNext_inr_iff (Q : ReactionNetwork X R)
    (anchor : IndexedMatching Q) (reactionOrder : List R) (r : R) (x : X) :
    Sum.inl x ∈ sourceExchangeNext Q anchor reactionOrder (Sum.inr r) ↔
      (x, r) ∈ anchor.edgeList := by
  simp [sourceExchangeNext]

theorem mem_sourceBoundaryStarts_iff (anchor : IndexedMatching Q)
    (speciesOrder : List X) (x : X) :
    Sum.inl x ∈ sourceBoundaryStarts anchor speciesOrder ↔
      x ∈ speciesOrder ∧ x ∉ anchor.species := by
  simp [sourceBoundaryStarts]

omit [DecidableEq X] in
theorem sourceBoundaryTarget_inr_eq_true_iff (anchor : IndexedMatching Q) (r : R) :
    sourceBoundaryTarget anchor (Sum.inr r) = true ↔ r ∉ anchor.reactions := by
  simp [sourceBoundaryTarget]

theorem sourceBoundaryStarts_nodup (anchor : IndexedMatching Q)
    (speciesOrder : List X) :
    (sourceBoundaryStarts anchor speciesOrder).Nodup :=
  List.nodup_dedup _

theorem sourcePathPacks_nodup [Fintype X] [Fintype R]
    (Q : ReactionNetwork X R) (anchor : IndexedMatching Q)
    (speciesOrder : List X) (reactionOrder : List R) :
    (sourcePathPacks Q anchor speciesOrder reactionOrder).Nodup := by
  exact nodup_directBoundaryPathPacks _ _ _
    (sourceBoundaryStarts_nodup anchor speciesOrder)
    (sourceExchangeNext_nodup Q anchor reactionOrder)

theorem sourcePathPacks_length_le [Fintype X] [Fintype R]
    (Q : ReactionNetwork X R) (anchor : IndexedMatching Q)
    (speciesOrder : List X) (reactionOrder : List R) :
    (sourcePathPacks Q anchor speciesOrder reactionOrder).length ≤
      2 ^ (directBoundaryPaths (sourceExchangeNext Q anchor reactionOrder)
        (sourceBoundaryTarget anchor)
        (sourceBoundaryStarts anchor speciesOrder)).length := by
  exact length_directBoundaryPathPacks_le _ _ _

theorem mem_sourceCandidates_iff [Fintype X] [Fintype R]
    (Q : ReactionNetwork X R) (anchor candidate : IndexedMatching Q)
    (speciesOrder : List X) (reactionOrder : List R) :
    candidate ∈ sourceCandidates Q anchor speciesOrder reactionOrder ↔
      ∃ pack ∈ sourcePathPacks Q anchor speciesOrder reactionOrder,
        buildPathPackCandidate? Q anchor pack = some candidate := by
  simp [sourceCandidates]

end ConcreteSearch

end AutocatalyticCS
