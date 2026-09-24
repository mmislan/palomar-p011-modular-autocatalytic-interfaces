import Mathlib

/-!
# Perron eigenvector of an entrywise-positive matrix

Original work: Michael Mislan, 2026. Licensed under Apache-2.0.

Independent replacement for the general fixed-point theorem previously used by
`PerronExistence`. This is the Collatz–Wielandt argument; no fixed-point theorem
is needed. Among pairs `(x, t)` with `x` a probability vector and
`t * x i ≤ (P x) i` for every `i`, compactness gives a pair maximizing `t`.
If `P x ≠ t x` at a maximizer, then positivity of `P` produces a strictly
better pair from the normalized vector `P x`. Hence `P x = t x`.
-/

namespace DegradationControl
namespace PositivePerron

open Finset

variable {ι : Type*} [Fintype ι]

/-- Probability vectors on a finite index type. -/
def simplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

theorem isCompact_simplex : IsCompact (simplex ι) := by
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : ι → ℝ)) (b := 1))
  · have h1 : IsClosed {x : ι → ℝ | ∀ i, 0 ≤ x i} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {x : ι → ℝ | ∑ i, x i = 1} :=
      isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    rw [simplex, Set.ofPred_and]
    exact h1.inter h2
  · rintro x ⟨hx0, hx1⟩
    refine ⟨fun i => hx0 i, fun i => ?_⟩
    have := Finset.single_le_sum (fun j _ => hx0 j) (Finset.mem_univ i)
    simpa [hx1] using this

/-- An entrywise-positive matrix sends a probability vector to a strictly
positive vector. -/
theorem sum_mul_pos {P : Matrix ι ι ℝ} (hP : ∀ i j, 0 < P i j) {x : ι → ℝ}
    (hx : x ∈ simplex ι) (i : ι) : 0 < ∑ j, P i j * x j := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨k, hk⟩ : ∃ k, 0 < x k := by
    by_contra h
    push Not at h
    have : ∑ j, x j = 0 := Finset.sum_eq_zero fun j _ => le_antisymm (h j) (hx0 j)
    rw [hx1] at this
    exact one_ne_zero this
  calc 0 < P i k * x k := mul_pos (hP i k) hk
    _ ≤ ∑ j, P i j * x j :=
      Finset.single_le_sum (f := fun j => P i j * x j)
        (fun j _ => mul_nonneg (hP i j).le (hx0 j)) (Finset.mem_univ k)

/-- Perron's theorem for an entrywise-positive real matrix: a positive
eigenvalue with a strictly positive eigenvector whose coordinates sum to one. -/
theorem exists_perron [Nonempty ι] {P : Matrix ι ι ℝ} (hP : ∀ i j, 0 < P i j) :
    ∃ rho : ℝ, 0 < rho ∧ ∃ v : ι → ℝ,
      (∀ i, 0 < v i) ∧ ∑ i, v i = 1 ∧ P.mulVec v = rho • v := by
  classical
  -- Any admissible `t` is bounded by the total mass of `P`.
  have hbound : ∀ x ∈ simplex ι, ∀ t : ℝ, (∀ i, t * x i ≤ ∑ j, P i j * x j) →
      t ≤ ∑ i, ∑ j, P i j := by
    rintro x ⟨hx0, hx1⟩ t ht
    have hxle : ∀ j, x j ≤ 1 := fun j => by
      have := Finset.single_le_sum (fun k _ => hx0 k) (Finset.mem_univ j)
      rwa [hx1] at this
    calc t = ∑ i, t * x i := by rw [← Finset.mul_sum, hx1, mul_one]
      _ ≤ ∑ i, ∑ j, P i j * x j := Finset.sum_le_sum fun i _ => ht i
      _ ≤ ∑ i, ∑ j, P i j := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          simpa using mul_le_mul_of_nonneg_left (hxle j) (hP i j).le
  -- The compact set of admissible pairs.
  let K : Set ((ι → ℝ) × ℝ) :=
    (simplex ι ×ˢ Set.Icc (0 : ℝ) (∑ i, ∑ j, P i j)) ∩
      {p | ∀ i, p.2 * p.1 i ≤ ∑ j, P i j * p.1 j}
  have hKc : IsCompact K := by
    have hprod := (isCompact_simplex (ι := ι)).prod
      (isCompact_Icc (a := (0 : ℝ)) (b := ∑ i, ∑ j, P i j))
    refine hprod.inter_right ?_
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le
      (continuous_snd.mul ((continuous_apply i).comp continuous_fst))
      (continuous_finsetSum _ fun j _ =>
        continuous_const.mul ((continuous_apply j).comp continuous_fst))
  have hKne : K.Nonempty := by
    refine ⟨(Pi.single (Classical.arbitrary ι) 1, 0), ⟨⟨⟨fun i => ?_, by simp⟩, ?_⟩, ?_⟩⟩
    · by_cases h : i = Classical.arbitrary ι <;> simp [h]
    · exact ⟨le_rfl, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => (hP i j).le⟩
    · intro i
      simp only [zero_mul]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hP i j).le (by
        by_cases h : j = Classical.arbitrary ι <;> simp [h])
  obtain ⟨⟨x, r⟩, ⟨⟨hxS, hr0⟩, hr⟩, hmax⟩ :=
    hKc.exists_isMaxOn hKne continuous_snd.continuousOn
  have hr : ∀ i, r * x i ≤ ∑ j, P i j * x j := hr
  obtain ⟨y, hy⟩ : ∃ y : ι → ℝ, ∀ i, y i = ∑ j, P i j * x j := ⟨_, fun _ => rfl⟩
  have ypos : ∀ i, 0 < y i := fun i => (hy i).symm ▸ sum_mul_pos hP hxS i
  -- At a maximizer, `x` is an eigenvector.
  have heq : ∀ i, y i = r * x i := by
    by_contra hne
    push Not at hne
    obtain ⟨k, hk⟩ := hne
    have hk' : r * x k < y k :=
      lt_of_le_of_ne (by rw [hy k]; exact hr k) (Ne.symm hk)
    have hgap : ∀ i, 0 < ∑ j, P i j * y j - r * y i := by
      intro i
      have e : ∑ j, P i j * (y j - r * x j) = ∑ j, P i j * y j - r * y i := by
        rw [hy i, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [← e]
      calc 0 < P i k * (y k - r * x k) := mul_pos (hP i k) (sub_pos.mpr hk')
        _ ≤ ∑ j, P i j * (y j - r * x j) :=
          Finset.single_le_sum (f := fun j => P i j * (y j - r * x j))
            (fun j _ => mul_nonneg (hP i j).le
              (sub_nonneg.mpr (by rw [hy j]; exact hr j)))
            (Finset.mem_univ k)
    obtain ⟨i0, -, hmin⟩ := Finset.exists_min_image Finset.univ
      (fun i => (∑ j, P i j * y j - r * y i) / y i) Finset.univ_nonempty
    set δ := (∑ j, P i0 j * y j - r * y i0) / y i0 with hδdef
    have hδpos : 0 < δ := div_pos (hgap i0) (ypos i0)
    have hδ : ∀ i, (r + δ) * y i ≤ ∑ j, P i j * y j := by
      intro i
      have h := (le_div_iff₀ (ypos i)).mp (hmin i (Finset.mem_univ i))
      linarith
    obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = ∑ i, y i := ⟨_, rfl⟩
    have hs : 0 < s := hs_def ▸ Finset.sum_pos (fun i _ => ypos i) Finset.univ_nonempty
    obtain ⟨z, hz_def⟩ : ∃ z : ι → ℝ, ∀ i, z i = y i / s := ⟨_, fun _ => rfl⟩
    have hzS : z ∈ simplex ι := by
      refine ⟨fun i => by rw [hz_def i]; exact div_nonneg (ypos i).le hs.le, ?_⟩
      simp only [hz_def]
      rw [← Finset.sum_div, ← hs_def, div_self hs.ne']
    have hz : ∀ i, (r + δ) * z i ≤ ∑ j, P i j * z j := by
      intro i
      have e1 : ∑ j, P i j * z j = (∑ j, P i j * y j) / s := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by rw [hz_def j]; ring
      rw [e1, hz_def i, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (hδ i) hs.le
    have hmem : (z, r + δ) ∈ K :=
      ⟨⟨hzS, by linarith [hr0.1], hbound z hzS (r + δ) hz⟩, hz⟩
    have := isMaxOn_iff.mp hmax _ hmem
    simp only at this
    linarith
  -- Conclude.
  have hrpos : 0 < r := by
    have hsum : ∑ i, y i = r := by
      rw [Finset.sum_congr rfl fun i _ => heq i, ← Finset.mul_sum, hxS.2, mul_one]
    rw [← hsum]
    exact Finset.sum_pos (fun i _ => ypos i) Finset.univ_nonempty
  refine ⟨r, hrpos, x, fun i => ?_, hxS.2, ?_⟩
  · have h := ypos i
    rw [heq i] at h
    exact pos_of_mul_pos_right h hrpos.le
  · ext i
    rw [Pi.smul_apply, smul_eq_mul, ← heq i, hy i]
    rfl

end PositivePerron
end DegradationControl
