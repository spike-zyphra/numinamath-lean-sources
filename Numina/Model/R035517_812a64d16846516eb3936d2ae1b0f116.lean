import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_190726 :
  IsLeast {M | ∃ a : Fin 7 → ℝ, (∀ i, 0 ≤ a i) ∧ (∑ i, a i) = 1 ∧
    M = max (max (max (max (a 0 + a 1 + a 2) (a 1 + a 2 + a 3)) (a 2 + a 3 + a 4)) (a 3 + a 4 + a 5)) (a 4 + a 5 + a 6)} (1/3) := by
  constructor
  · -- Show that 1/3 is in the set
    use λ i =>
      match i with
      | 0 => (1 / 3 : ℝ)
      | 1 => (0 : ℝ)
      | 2 => (0 : ℝ)
      | 3 => (1 / 3 : ℝ)
      | 4 => (0 : ℝ)
      | 5 => (0 : ℝ)
      | 6 => (1 / 3 : ℝ)
      | _ => (0 : ℝ)
    constructor
    · -- Show all values are non-negative
      intro i
      fin_cases i <;> norm_num
    constructor
    · -- Show the sum is 1
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
      all_goals norm_num
    · -- Show M = 1/3
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
      all_goals norm_num
  · -- Show that 1/3 is the smallest
    intro M h
    rcases h with ⟨a, ha, hsum, hM⟩
    have h1 : a 0 + a 1 + a 2 ≤ M := by
      simp [hM, max_le_iff]
    have h2 : a 1 + a 2 + a 3 ≤ M := by
      simp [hM, max_le_iff]
    have h3 : a 2 + a 3 + a 4 ≤ M := by
      simp [hM, max_le_iff]
    have h4 : a 3 + a 4 + a 5 ≤ M := by
      simp [hM, max_le_iff]
    have h5 : a 4 + a 5 + a 6 ≤ M := by
      simp [hM, max_le_iff]
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hsum
    by_contra h
    push_neg at h
    have h1' : a 0 + a 1 + a 2 < 1 / 3 := by
      linarith
    have h2' : a 1 + a 2 + a 3 < 1 / 3 := by
      linarith
    have h3' : a 2 + a 3 + a 4 < 1 / 3 := by
      linarith
    have h4' : a 3 + a 4 + a 5 < 1 / 3 := by
      linarith
    have h5' : a 4 + a 5 + a 6 < 1 / 3 := by
      linarith
    nlinarith [h1', h2', h3', h4', h5', hsum, ha 0, ha 1, ha 2, ha 3, ha 4, ha 5, ha 6]