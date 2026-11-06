import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_232626 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = min (min (4 * x + 1) (x + 2)) (-2 * x + 4)) :
  IsGreatest (range f) (8 / 3) := by
  constructor
  · -- Show that 8/3 is in the range of f
    use 2 / 3
    rw [h₀]
    norm_num [min_eq_left, min_eq_right]
    all_goals norm_num
  · -- Show that 8/3 is the greatest value of f
    intro y
    rintro ⟨x, hx⟩
    rw [h₀] at hx
    by_cases h1 : 4 * x + 1 ≤ x + 2
    · -- Case where 4x + 1 is less than x + 2
      have h2 : min (4 * x + 1) (x + 2) = 4 * x + 1 := by apply min_eq_left; linarith
      rw [h2] at hx
      by_cases h3 : 4 * x + 1 ≤ -2 * x + 4
      · -- Case where 4x + 1 is also less than -2x + 4
        have h4 : min (4 * x + 1) (-2 * x + 4) = 4 * x + 1 := by apply min_eq_left; linarith
        rw [h4] at hx
        linarith
      · -- Case where -2x + 4 is less than 4x + 1
        have h4 : min (4 * x + 1) (-2 * x + 4) = -2 * x + 4 := by apply min_eq_right; linarith
        rw [h4] at hx
        linarith
    · -- Case where x + 2 is less than 4x + 1
      have h2 : min (4 * x + 1) (x + 2) = x + 2 := by apply min_eq_right; linarith
      rw [h2] at hx
      by_cases h3 : x + 2 ≤ -2 * x + 4
      · -- Case where x + 2 is also less than -2x + 4
        have h4 : min (x + 2) (-2 * x + 4) = x + 2 := by apply min_eq_left; linarith
        rw [h4] at hx
        linarith
      · -- Case where -2x + 4 is less than x + 2
        have h4 : min (x + 2) (-2 * x + 4) = -2 * x + 4 := by apply min_eq_right; linarith
        rw [h4] at hx
        linarith