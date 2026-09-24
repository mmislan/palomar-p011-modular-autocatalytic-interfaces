import proofs.AutocatalyticCS.AnchorExchangeDAG
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
An executable include/exclude enumerator for vertex-disjoint path packs.  Its
input is the list of directed boundary paths produced by a DAG path search; it
never enumerates ambient subgraphs.  Packs retain the input order, giving a
canonical search representation.
-/

namespace AutocatalyticCS

variable {V : Type*} [DecidableEq V]

/-- Semantic recursion specification for a directed path search.  `visited`
contains vertices used before `current`; successors must avoid both. -/
def IsDirectPath (next : V → List V) (target : V → Bool) :
    Nat → List V → V → List V → Prop
  | 0, _visited, current, path =>
      target current = true ∧ path = [current]
  | fuel + 1, visited, current, path =>
      (target current = true ∧ path = [current]) ∨
      (target current = false ∧
        ∃ successor ∈ next current,
          successor ∉ current :: visited ∧
          ∃ tail, IsDirectPath next target fuel (current :: visited) successor tail ∧
            path = current :: tail)

/-- Fuel-bounded neighbor DFS.  It stops on the first boundary target and never
revisits a vertex on the active branch. -/
def directPathsAux (next : V → List V) (target : V → Bool) :
    Nat → List V → V → List (List V)
  | 0, _visited, current =>
      if target current then [[current]] else []
  | fuel + 1, visited, current =>
      if target current then [[current]]
      else
        (next current).filter (fun successor => successor ∉ current :: visited)
          |>.flatMap fun successor =>
            (directPathsAux next target fuel (current :: visited) successor).map
              (current :: ·)

theorem mem_directPathsAux_iff (next : V → List V) (target : V → Bool)
    (fuel : Nat) (visited : List V) (current : V) (path : List V) :
    path ∈ directPathsAux next target fuel visited current ↔
      IsDirectPath next target fuel visited current path := by
  induction fuel generalizing visited current path with
  | zero =>
      by_cases htarget : target current = true
      · simp [directPathsAux, IsDirectPath, htarget]
      · simp [directPathsAux, IsDirectPath, htarget]
  | succ fuel ih =>
      by_cases htarget : target current = true
      · simp [directPathsAux, IsDirectPath, htarget]
      · simp [directPathsAux, IsDirectPath, htarget, ih]
        constructor
        · rintro ⟨successor, ⟨⟨hnext, hne, hfresh⟩, tail, htail, heq⟩⟩
          exact ⟨successor, hnext, ⟨hne, hfresh⟩, tail, htail, heq.symm⟩
        · rintro ⟨successor, hnext, ⟨hne, hfresh⟩, tail, htail, heq⟩
          exact ⟨successor, ⟨⟨hnext, hne, hfresh⟩, tail, htail, heq.symm⟩⟩

/-- Finite entry point: a simple path in a finite vertex type uses at most one
vertex per recursion level. -/
def directPaths [Fintype V] (next : V → List V) (target : V → Bool)
    (start : V) : List (List V) :=
  directPathsAux next target (Fintype.card V) [] start

theorem mem_directPaths_iff [Fintype V] (next : V → List V)
    (target : V → Bool) (start : V) (path : List V) :
    path ∈ directPaths next target start ↔
      IsDirectPath next target (Fintype.card V) [] start path := by
  exact mem_directPathsAux_iff next target _ _ _ _

/-- Every consecutive pair in an ordered vertex list follows the supplied
successor table. -/
def Follows (next : V → List V) : List V → Prop
  | a :: b :: tail => b ∈ next a ∧ Follows next (b :: tail)
  | _ => True

omit [DecidableEq V] in
/-- A simple graph walk whose last vertex is the first target is represented
by the executable DFS whenever the fuel dominates its edge length. -/
theorem isDirectPath_support_of_walk {G : _root_.SimpleGraph V}
    (next : V → List V) (target : V → Bool)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hfollow : Follows next p.support)
    (htarget : target v = true)
    (hinternal : ∀ w ∈ p.support, w ≠ v → target w = false)
    (fuel : Nat) (visited : List V) (hfuel : p.length ≤ fuel)
    (hdisjoint : List.Disjoint p.support visited) :
    IsDirectPath next target fuel visited u p.support := by
  induction p generalizing fuel visited with
  | nil =>
      cases fuel with
      | zero => exact ⟨htarget, rfl⟩
      | succ fuel => exact Or.inl ⟨htarget, rfl⟩
  | @cons u w v huw q ih =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have hfollow' : w ∈ next u ∧ Follows next q.support := by
            cases q <;> simpa [Follows] using hfollow
          have hpq : q.IsPath := hp.of_cons
          have huq : u ∉ q.support :=
            (SimpleGraph.Walk.cons_isPath_iff huw q).mp hp |>.2
          have huv : u ≠ v := by
            intro huv
            subst v
            exact huq (by simp)
          have hwvisited : w ∉ visited := by
            intro hw
            exact hdisjoint (by simp) hw
          have htaildisjoint : List.Disjoint q.support (u :: visited) := by
            rw [List.disjoint_left]
            intro z hz
            simp only [List.mem_cons]
            rintro (rfl | hzvisited)
            · exact huq hz
            · exact hdisjoint (by simp [hz]) hzvisited
          refine Or.inr ⟨hinternal u (by simp) huv, w, hfollow'.1,
            ?_, q.support, ?_, rfl⟩
          · intro hw
            rcases List.mem_cons.mp hw with hwu | hwvisited'
            · exact huw.ne hwu.symm
            · exact hwvisited hwvisited'
          exact ih hpq hfollow'.2 htarget
            (fun z hz hzv => hinternal z (by simp [hz]) hzv)
            fuel (u :: visited) (by simpa using hfuel) htaildisjoint

omit [DecidableEq V] in
private theorem directPath_head (next : V → List V) (target : V → Bool)
    {fuel : Nat} {visited : List V} {current : V} {path : List V}
    (h : IsDirectPath next target fuel visited current path) :
    path.head? = some current := by
  cases fuel with
  | zero =>
      rcases h with ⟨_, rfl⟩
      rfl
  | succ fuel =>
      rcases h with hterminal | hstep
      · rcases hterminal with ⟨_, rfl⟩
        rfl
      · rcases hstep with ⟨successor, _, _, _, tail, _, rfl⟩
        rfl

theorem nodup_directPathsAux (next : V → List V) (target : V → Bool)
    (hnext : ∀ v, (next v).Nodup) (fuel : Nat) (visited : List V) (current : V) :
    (directPathsAux next target fuel visited current).Nodup := by
  induction fuel generalizing visited current with
  | zero =>
      by_cases htarget : target current = true
      · simp [directPathsAux, htarget]
      · simp [directPathsAux, htarget]
  | succ fuel ih =>
      by_cases htarget : target current = true
      · simp [directPathsAux, htarget]
      · simp only [directPathsAux, htarget, Bool.false_eq_true, ↓reduceIte]
        apply List.nodup_flatMap.2
        constructor
        · intro successor hsuccessor
          exact (ih (current :: visited) successor).map fun _ _ h => List.cons.inj h |>.2
        · have hsuccessors :
              ((next current).filter fun successor => successor ∉ current :: visited).Nodup :=
            (hnext current).filter _
          refine hsuccessors.imp fun {a b} hab => ?_
          rw [Function.onFun_apply, List.disjoint_left]
          intro path hpatha hpathb
          rcases List.mem_map.1 hpatha with ⟨taila, htaila, rfl⟩
          rcases List.mem_map.1 hpathb with ⟨tailb, htailb, heq⟩
          have htails : taila = tailb := (List.cons.inj heq |>.2).symm
          have hheada := directPath_head next target
            ((mem_directPathsAux_iff next target fuel (current :: visited) a taila).1 htaila)
          have hheadb := directPath_head next target
            ((mem_directPathsAux_iff next target fuel (current :: visited) b tailb).1 htailb)
          rw [htails, hheadb] at hheada
          exact hab (Option.some.inj hheada.symm)

theorem nodup_directPaths [Fintype V] (next : V → List V) (target : V → Bool)
    (hnext : ∀ v, (next v).Nodup) (start : V) :
    (directPaths next target start).Nodup :=
  nodup_directPathsAux next target hnext _ _ _

/-- Enumerate from every boundary source.  The source order and adjacency-list
order canonically determine the output order. -/
def directBoundaryPaths [Fintype V] (next : V → List V) (target : V → Bool)
    (starts : List V) : List (List V) :=
  starts.flatMap (directPaths next target)

theorem mem_directBoundaryPaths_iff [Fintype V] (next : V → List V)
    (target : V → Bool) (starts : List V) (path : List V) :
    path ∈ directBoundaryPaths next target starts ↔
      ∃ start ∈ starts,
        IsDirectPath next target (Fintype.card V) [] start path := by
  simp [directBoundaryPaths, mem_directPaths_iff]

theorem nodup_directBoundaryPaths [Fintype V] (next : V → List V)
    (target : V → Bool) (starts : List V) (hstarts : starts.Nodup)
    (hnext : ∀ v, (next v).Nodup) :
    (directBoundaryPaths next target starts).Nodup := by
  rw [directBoundaryPaths, List.nodup_flatMap]
  refine ⟨fun start _ => nodup_directPaths next target hnext start,
    hstarts.imp fun {a b} hab => ?_⟩
  rw [Function.onFun_apply, List.disjoint_left]
  intro path hpatha hpathb
  have hheada := directPath_head next target
    ((mem_directPaths_iff next target a path).1 hpatha)
  have hheadb := directPath_head next target
    ((mem_directPaths_iff next target b path).1 hpathb)
  rw [hheadb] at hheada
  exact hab (Option.some.inj hheada.symm)

def PathCompatible (p : Finset V) (pack : List (Finset V)) : Bool :=
  pack.all fun q => decide (Disjoint p q)

theorem pathCompatible_eq_true_iff (p : Finset V) (pack : List (Finset V)) :
    PathCompatible p pack = true ↔ ∀ q ∈ pack, Disjoint p q := by
  simp [PathCompatible]

/-- Direct include/exclude DFS over a list of candidate directed paths. -/
def directDisjointPacks : List (Finset V) → List (List (Finset V))
  | [] => [[]]
  | p :: paths =>
      let rest := directDisjointPacks paths
      rest ++ (rest.filter (PathCompatible p)).map (p :: ·)

theorem mem_directDisjointPacks_iff (paths pack : List (Finset V)) :
    pack ∈ directDisjointPacks paths ↔
      pack.Sublist paths ∧ pack.Pairwise Disjoint := by
  induction paths generalizing pack with
  | nil =>
      constructor
      · intro h
        have hp : pack = [] := by simpa [directDisjointPacks] using h
        subst pack
        simp
      · rintro ⟨hsub, _hpair⟩
        have hp : pack = [] := by cases hsub; rfl
        subst pack
        simp [directDisjointPacks]
  | cons p paths ih =>
      simp only [directDisjointPacks, List.mem_append, List.mem_map,
        List.mem_filter, pathCompatible_eq_true_iff]
      constructor
      · rintro (hskip | ⟨candidate, ⟨hcandidate, hcompat⟩, rfl⟩)
        · obtain ⟨hsub, hpair⟩ := (ih pack).mp hskip
          exact ⟨hsub.cons p, hpair⟩
        · obtain ⟨hsub, hpair⟩ := (ih candidate).mp hcandidate
          exact ⟨hsub.cons_cons p, List.pairwise_cons.2 ⟨hcompat, hpair⟩⟩
      · rintro ⟨hsub, hpair⟩
        match pack with
        | [] =>
            left
            exact (ih []).2 (by simp)
        | q :: qs =>
            rcases List.cons_sublist_cons'.1 hsub with hskip | ⟨hqp, htake⟩
            · left
              exact (ih (q :: qs)).2 ⟨hskip, hpair⟩
            · subst q
              right
              refine ⟨qs, ⟨(ih qs).2 ⟨htake, List.pairwise_cons.1 hpair |>.2⟩, ?_⟩, rfl⟩
              exact List.pairwise_cons.1 hpair |>.1

theorem nodup_directDisjointPacks (paths : List (Finset V)) (hpaths : paths.Nodup) :
    (directDisjointPacks paths).Nodup := by
  induction paths with
  | nil => simp [directDisjointPacks]
  | cons p paths ih =>
      have hp : p ∉ paths := List.nodup_cons.1 hpaths |>.1
      have hrest : paths.Nodup := List.nodup_cons.1 hpaths |>.2
      have ih' := ih hrest
      rw [directDisjointPacks, List.nodup_append]
      refine ⟨ih', (ih'.filter _).map fun _ _ h => List.cons.inj h |>.2, ?_⟩
      intro pack hpack taken htake
      rcases List.mem_map.1 htake with ⟨candidate, hc, rfl⟩
      have hsub : pack.Sublist paths :=
        (mem_directDisjointPacks_iff paths pack).1 hpack |>.1
      intro heq
      have hpin : p ∈ pack := by rw [heq]; simp
      exact hp (hsub.subset hpin)

/-- The direct recursion tree is bounded by the number of subsets of the
*candidate path list*, not by the number of ambient subgraphs. -/
theorem length_directDisjointPacks_le (paths : List (Finset V)) :
    (directDisjointPacks paths).length ≤ 2 ^ paths.length := by
  induction paths with
  | nil => simp [directDisjointPacks]
  | cons p paths ih =>
      simp only [directDisjointPacks, List.length_append, List.length_map,
        List.length_cons]
      calc
        (directDisjointPacks paths).length +
            (List.filter (PathCompatible p) (directDisjointPacks paths)).length
          ≤ (directDisjointPacks paths).length +
              (directDisjointPacks paths).length :=
            Nat.add_le_add_left (List.length_filter_le _ _) _
        _ ≤ 2 ^ paths.length + 2 ^ paths.length := Nat.add_le_add ih ih
        _ = 2 ^ (paths.length + 1) := by rw [pow_succ]; omega

def OrderedPathCompatible (p : List V) (pack : List (List V)) : Bool :=
  pack.all fun q => decide (Disjoint p.toFinset q.toFinset)

theorem orderedPathCompatible_eq_true_iff (p : List V) (pack : List (List V)) :
    OrderedPathCompatible p pack = true ↔
      ∀ q ∈ pack, Disjoint p.toFinset q.toFinset := by
  simp [OrderedPathCompatible]

/-- Include/exclude DFS that retains each path as an ordered vertex list.  Thus
distinct path representations are never identified by a set conversion. -/
def directOrderedPathPacks : List (List V) → List (List (List V))
  | [] => [[]]
  | p :: paths =>
      let rest := directOrderedPathPacks paths
      rest ++ (rest.filter (OrderedPathCompatible p)).map (p :: ·)

theorem mem_directOrderedPathPacks_iff (paths pack : List (List V)) :
    pack ∈ directOrderedPathPacks paths ↔
      pack.Sublist paths ∧
        pack.Pairwise fun p q => Disjoint p.toFinset q.toFinset := by
  induction paths generalizing pack with
  | nil =>
      constructor
      · intro h
        have hp : pack = [] := by simpa [directOrderedPathPacks] using h
        subst pack
        simp
      · rintro ⟨hsub, _⟩
        have hp : pack = [] := by cases hsub; rfl
        subst pack
        simp [directOrderedPathPacks]
  | cons p paths ih =>
      simp only [directOrderedPathPacks, List.mem_append, List.mem_map,
        List.mem_filter, orderedPathCompatible_eq_true_iff]
      constructor
      · rintro (hskip | ⟨candidate, ⟨hcandidate, hcompat⟩, rfl⟩)
        · obtain ⟨hsub, hpair⟩ := (ih pack).mp hskip
          exact ⟨hsub.cons p, hpair⟩
        · obtain ⟨hsub, hpair⟩ := (ih candidate).mp hcandidate
          exact ⟨hsub.cons_cons p, List.pairwise_cons.2 ⟨hcompat, hpair⟩⟩
      · rintro ⟨hsub, hpair⟩
        match pack with
        | [] =>
            left
            exact (ih []).2 (by simp)
        | q :: qs =>
            rcases List.cons_sublist_cons'.1 hsub with hskip | ⟨hqp, htake⟩
            · left
              exact (ih (q :: qs)).2 ⟨hskip, hpair⟩
            · subst q
              right
              refine ⟨qs, ⟨(ih qs).2 ⟨htake, List.pairwise_cons.1 hpair |>.2⟩, ?_⟩, rfl⟩
              exact List.pairwise_cons.1 hpair |>.1

theorem nodup_directOrderedPathPacks (paths : List (List V)) (hpaths : paths.Nodup) :
    (directOrderedPathPacks paths).Nodup := by
  induction paths with
  | nil => simp [directOrderedPathPacks]
  | cons p paths ih =>
      have hp : p ∉ paths := List.nodup_cons.1 hpaths |>.1
      have hrest : paths.Nodup := List.nodup_cons.1 hpaths |>.2
      have ih' := ih hrest
      rw [directOrderedPathPacks, List.nodup_append]
      refine ⟨ih', (ih'.filter _).map fun _ _ h => List.cons.inj h |>.2, ?_⟩
      intro pack hpack taken htake
      rcases List.mem_map.1 htake with ⟨candidate, _, rfl⟩
      have hsub : pack.Sublist paths :=
        (mem_directOrderedPathPacks_iff paths pack).1 hpack |>.1
      intro heq
      have hpin : p ∈ pack := by rw [heq]; simp
      exact hp (hsub.subset hpin)

theorem length_directOrderedPathPacks_le (paths : List (List V)) :
    (directOrderedPathPacks paths).length ≤ 2 ^ paths.length := by
  induction paths with
  | nil => simp [directOrderedPathPacks]
  | cons p paths ih =>
      simp only [directOrderedPathPacks, List.length_append, List.length_map,
        List.length_cons]
      calc
        (directOrderedPathPacks paths).length +
            (List.filter (OrderedPathCompatible p) (directOrderedPathPacks paths)).length
          ≤ (directOrderedPathPacks paths).length +
              (directOrderedPathPacks paths).length :=
            Nat.add_le_add_left (List.length_filter_le _ _) _
        _ ≤ 2 ^ paths.length + 2 ^ paths.length := Nat.add_le_add ih ih
        _ = 2 ^ (paths.length + 1) := by rw [pow_succ]; omega

/-- Complete direct boundary-path-pack enumerator. -/
def directBoundaryPathPacks [Fintype V] (next : V → List V)
    (target : V → Bool) (starts : List V) : List (List (List V)) :=
  directOrderedPathPacks (directBoundaryPaths next target starts)

theorem mem_directBoundaryPathPacks_iff [Fintype V] (next : V → List V)
    (target : V → Bool) (starts : List V) (pack : List (List V)) :
    pack ∈ directBoundaryPathPacks next target starts ↔
      pack.Sublist (directBoundaryPaths next target starts) ∧
        pack.Pairwise fun p q => Disjoint p.toFinset q.toFinset := by
  exact mem_directOrderedPathPacks_iff _ _

theorem nodup_directBoundaryPathPacks [Fintype V] (next : V → List V)
    (target : V → Bool) (starts : List V) (hstarts : starts.Nodup)
    (hnext : ∀ v, (next v).Nodup) :
    (directBoundaryPathPacks next target starts).Nodup :=
  nodup_directOrderedPathPacks _
    (nodup_directBoundaryPaths next target starts hstarts hnext)

theorem length_directBoundaryPathPacks_le [Fintype V] (next : V → List V)
    (target : V → Bool) (starts : List V) :
    (directBoundaryPathPacks next target starts).length ≤
      2 ^ (directBoundaryPaths next target starts).length := by
  exact length_directOrderedPathPacks_le _

end AutocatalyticCS
