import Mathlib

/-!
# Gordan's alternative over the rationals

Original work: Michael Mislan, 2026. Licensed under Apache-2.0.

For a finite rational matrix `M`, either some rational vector `x` makes every
row strictly positive, `0 < ∑ k, M i k * x k`, or some nonnegative, nonzero
rational row combination vanishes, `∑ i, y i * M i k = 0`. The proof is exact
Fourier–Motzkin elimination of one variable at a time. It never passes through
the reals or uses density: each eliminated system is a nonnegative rational
combination of the previous one, and a rational value for the eliminated
variable is chosen between finitely many rational bounds.
-/

namespace AutocatalyticCS
namespace RationalGordan

open Finset

/-- Finitely many strict lower bounds below finitely many strict upper bounds
leave room for a rational point strictly between them. -/
theorem exists_between_finsets (S T : Finset ℚ) (h : ∀ s ∈ S, ∀ t ∈ T, s < t) :
    ∃ r : ℚ, (∀ s ∈ S, s < r) ∧ ∀ t ∈ T, r < t := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · rcases T.eq_empty_or_nonempty with rfl | hT
    · exact ⟨0, by simp, by simp⟩
    · refine ⟨T.min' hT - 1, by simp, fun t ht => ?_⟩
      have := T.min'_le t ht
      linarith
  · rcases T.eq_empty_or_nonempty with rfl | hT
    · refine ⟨S.max' hS + 1, fun s hs => ?_, by simp⟩
      have := S.le_max' s hs
      linarith
    · have hlt : S.max' hS < T.min' hT := h _ (S.max'_mem hS) _ (T.min'_mem hT)
      refine ⟨(S.max' hS + T.min' hT) / 2, fun s hs => ?_, fun t ht => ?_⟩
      · have := S.le_max' s hs
        linarith
      · have := T.min'_le t ht
        linarith

universe u

/-- Gordan's alternative with `Fin n` columns, by induction on `n`. -/
theorem gordan_fin : ∀ (n : ℕ) {ι : Type u} [Fintype ι] (M : ι → Fin n → ℚ),
    (¬ ∃ x : Fin n → ℚ, ∀ i, 0 < ∑ j, M i j * x j) →
    ∃ y : ι → ℚ, (∀ i, 0 ≤ y i) ∧ (∃ i, 0 < y i) ∧ ∀ j, ∑ i, y i * M i j = 0 := by
  intro n
  induction n with
  | zero =>
    intro ι _ M hM
    by_cases hι : Nonempty ι
    · obtain ⟨i₀⟩ := hι
      exact ⟨fun _ => 1, fun _ => zero_le_one, ⟨i₀, one_pos⟩, fun j => j.elim0⟩
    · exact absurd ⟨fun j => j.elim0, fun i => (hι ⟨i⟩).elim⟩ hM
  | succ n ih =>
    intro ι _ M hM
    classical
    -- Coefficient of the eliminated (last) variable in each row.
    let c : ι → ℚ := fun i => M i (Fin.last n)
    let P := {i : ι // 0 < c i}
    let N := {i : ι // c i < 0}
    let Z := {i : ι // c i = 0}
    -- Nonnegative weights expressing each eliminated row as a combination of
    -- original rows: zero-coefficient rows are kept, and each positive/negative
    -- pair is combined so that the last coefficient cancels.
    let w : Z ⊕ (P × N) → ι → ℚ :=
      Sum.elim (fun z i => if z.1 = i then 1 else 0)
        (fun pq i => (if pq.1.1 = i then -c pq.2.1 else 0) +
          (if pq.2.1 = i then c pq.1.1 else 0))
    let M' : Z ⊕ (P × N) → Fin n → ℚ := fun r j => ∑ i, w r i * M i j.castSucc
    have hw_nonneg : ∀ r i, 0 ≤ w r i := by
      rintro (z | ⟨p, q⟩) i
      · simp only [w, Sum.elim_inl]
        split_ifs <;> norm_num
      · have hp : 0 < c p.1 := p.2
        have hq : c q.1 < 0 := q.2
        simp only [w, Sum.elim_inr]
        split_ifs <;> linarith
    have hw_apply : ∀ r (g : ι → ℚ), ∑ i, w r i * g i =
        Sum.elim (fun z : Z => g z.1)
          (fun pq : P × N => -c pq.2.1 * g pq.1.1 + c pq.1.1 * g pq.2.1) r := by
      rintro (z | ⟨p, q⟩) g
      · simp [w]
      · simp [w, add_mul, Finset.sum_add_distrib]
    have hw_last : ∀ r, ∑ i, w r i * c i = 0 := by
      rintro (z | ⟨p, q⟩)
      · rw [hw_apply]
        exact z.2
      · rw [hw_apply]
        simp only [Sum.elim_inr]
        ring
    -- If the eliminated system were feasible, so would the original one be.
    have hM' : ¬ ∃ x' : Fin n → ℚ, ∀ r, 0 < ∑ j, M' r j * x' j := by
      rintro ⟨x', hx'⟩
      apply hM
      let s : ι → ℚ := fun i => ∑ j, M i j.castSucc * x' j
      have key : ∀ r, ∑ j, M' r j * x' j = ∑ i, w r i * s i := by
        intro r
        simp only [M', s, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      have hz : ∀ z : Z, 0 < s z.1 := by
        intro z
        have := hx' (Sum.inl z)
        rwa [key, hw_apply] at this
      have hpq : ∀ (p : P) (q : N), 0 < -c q.1 * s p.1 + c p.1 * s q.1 := by
        intro p q
        have := hx' (Sum.inr (p, q))
        rwa [key, hw_apply] at this
      obtain ⟨t, ht_lower, ht_upper⟩ := exists_between_finsets
        (univ.image fun p : P => -s p.1 / c p.1)
        (univ.image fun q : N => -s q.1 / c q.1) (by
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
          have hp : 0 < c p.1 := p.2
          have hq : c q.1 < 0 := q.2
          set a := -s p.1 / c p.1 with ha_def
          set b := -s q.1 / c q.1 with hb_def
          have ha : a * c p.1 = -s p.1 := div_mul_cancel₀ _ (ne_of_gt hp)
          have hb : b * c q.1 = -s q.1 := div_mul_cancel₀ _ (ne_of_lt hq)
          have hid : -c q.1 * s p.1 + c p.1 * s q.1 = c p.1 * c q.1 * (a - b) := by
            rw [show s p.1 = -(a * c p.1) by linarith,
              show s q.1 = -(b * c q.1) by linarith]
            ring
          have hpos := hpq p q
          rw [hid] at hpos
          rcases pos_and_pos_or_neg_and_neg_of_mul_pos hpos with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact absurd h1 (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hp.le hq.le))
          · linarith)
      refine ⟨Fin.snoc (α := fun _ => ℚ) x' t, fun i => ?_⟩
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      change 0 < s i + c i * t
      rcases lt_trichotomy (c i) 0 with hneg | hzero | hpos
      · have hbound := ht_upper _ (Finset.mem_image_of_mem _ (Finset.mem_univ (⟨i, hneg⟩ : N)))
        have hcancel : c i * (-s i / c i) = -s i := mul_div_cancel₀ _ (ne_of_lt hneg)
        have := mul_lt_mul_of_neg_left hbound hneg
        linarith
      · have := hz ⟨i, hzero⟩
        rw [hzero]
        simpa using this
      · have hbound := ht_lower _ (Finset.mem_image_of_mem _ (Finset.mem_univ (⟨i, hpos⟩ : P)))
        have hcancel : c i * (-s i / c i) = -s i := mul_div_cancel₀ _ (ne_of_gt hpos)
        have := mul_lt_mul_of_pos_left hbound hpos
        linarith
    obtain ⟨y', hy'_nonneg, ⟨r₀, hr₀⟩, hy'⟩ := ih M' hM'
    -- Pull the certificate back to the original rows.
    let y : ι → ℚ := fun i => ∑ r, y' r * w r i
    have hswap : ∀ g : ι → ℚ, ∑ i, y i * g i = ∑ r, y' r * ∑ i, w r i * g i := by
      intro g
      simp only [y, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    have hy_nonneg : ∀ i, 0 ≤ y i := fun i =>
      Finset.sum_nonneg fun r _ => mul_nonneg (hy'_nonneg r) (hw_nonneg r i)
    have hy_ge : ∀ r i, y' r * w r i ≤ y i := fun r i =>
      Finset.single_le_sum (f := fun r => y' r * w r i)
        (fun r _ => mul_nonneg (hy'_nonneg r) (hw_nonneg r i)) (Finset.mem_univ r)
    refine ⟨y, hy_nonneg, ?_, fun j => ?_⟩
    · rcases r₀ with z | ⟨p, q⟩
      · refine ⟨z.1, lt_of_lt_of_le ?_ (hy_ge (Sum.inl z) z.1)⟩
        simpa [w] using hr₀
      · have hp : 0 < c p.1 := p.2
        have hq : c q.1 < 0 := q.2
        have hne : q.1 ≠ p.1 := fun h => by
          have : c q.1 = c p.1 := by rw [h]
          linarith
        refine ⟨p.1, lt_of_lt_of_le ?_ (hy_ge (Sum.inr (p, q)) p.1)⟩
        have hw : w (Sum.inr (p, q)) p.1 = -c q.1 := by
          simp [w, hne]
        rw [hw]
        exact mul_pos hr₀ (by linarith)
    · rw [hswap]
      refine Fin.lastCases ?_ (fun j => ?_) j
      · exact Finset.sum_eq_zero fun r _ => by rw [hw_last r, mul_zero]
      · exact hy' j

/-- **Gordan's alternative over `ℚ`.** If no rational vector makes every row of
`M` strictly positive, then a nonnegative, nonzero rational combination of the
rows of `M` is zero. -/
theorem gordan {ι κ : Type*} [Fintype ι] [Fintype κ] (M : ι → κ → ℚ)
    (h : ¬ ∃ x : κ → ℚ, ∀ i, 0 < ∑ k, M i k * x k) :
    ∃ y : ι → ℚ, (∀ i, 0 ≤ y i) ∧ (∃ i, 0 < y i) ∧ ∀ k, ∑ i, y i * M i k = 0 := by
  classical
  let e := Fintype.equivFin κ
  obtain ⟨y, hy_nonneg, hy_pos, hy⟩ :=
    gordan_fin (Fintype.card κ) (fun i j => M i (e.symm j)) (by
      rintro ⟨x, hx⟩
      refine h ⟨fun k => x (e k), fun i => ?_⟩
      have := hx i
      rw [← e.sum_comp] at this
      simpa using this)
  exact ⟨y, hy_nonneg, hy_pos, fun k => by simpa using hy (e k)⟩

end RationalGordan
end AutocatalyticCS
