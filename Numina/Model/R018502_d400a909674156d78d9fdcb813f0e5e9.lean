import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_2507 (y : ℝ → ℝ) (hy : y = λ x => min (min (4 * x + 1) (x + 2)) (-2 * x + 4)) :
    IsGreatest (range y) (8 / 3) := by
  have h1 : ∀ x, y x = min (min (4 * x + 1) (x + 2)) (-2 * x + 4) := by
    intro x
    rw [hy]
  constructor
  · -- Show that 8/3 is in the range of y
    use 2 / 3
    rw [h1]
    norm_num [min_eq_right, min_eq_left]
  · -- Show that 8/3 is the greatest element in the range
    intro r hr
    rcases hr with ⟨x, hx⟩
    rw [h1 x] at hx
    by_cases h2 : (4 * x + 1 : ℝ) ≤ (x + 2 : ℝ)
    · -- Case where 4x + 1 ≤ x + 2, so min(4x + 1, x + 2) = 4x + 1
      have h3 : min (4 * x + 1) (x + 2) = 4 * x + 1 := by
        apply min_eq_left
        linarith
      rw [h3] at hx
      by_cases h4 : (4 * x + 1 : ℝ) ≤ (-2 * x + 4 : ℝ)
      · -- Case where min = 4x + 1
        have h5 : min (4 * x + 1) (-2 * x + 4) = 4 * x + 1 := by
          apply min_eq_left
          linarith
        rw [h5] at hx
        nlinarith
      · -- Case where min = -2x + 4
        have h6 : min (4 * x + 1) (-2 * x + 4) = -2 * x + 4 := by
          apply min_eq_right
          nlinarith
        rw [h6] at hx
        nlinarith
    · -- Case where 4x + 1 > x + 2, so min(4x + 1, x + 2) = x + 2
      have h4 : min (4 * x + 1) (x + 2) = x + 2 := by
        apply min_eq_right
        linarith
      rw [h4] at hx
      by_cases h5 : (x + 2 : ℝ) ≤ (-2 * x + 4 : ℝ)
      · -- Case where min = x + 2
        have h6 : min (x + 2) (-2 * x + 4) = x + 2 := by
          apply min_eq_left
          linarith
        rw [h6] at hx
        nlinarith
      · -- Case where min = -2x + 4
        have h7 : min (x + 2) (-2 * x + 4) = -2 * x + 4 := by
          apply min_eq_right
          linarith
        rw [h7] at hx
        nlinarith