import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_245226 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = min (min (4 * x + 1) (x + 2)) (-2 * x + 4)) :
  IsGreatest (range f) (8 / 3) := by
  constructor
  · -- Show 8/3 is in the range of f, i.e., there exists an x such that f(x) = 8/3.
    use 2 / 3
    norm_num [h₀]
  · -- Show 8/3 is the greatest value in the range of f
    intro y
    rintro ⟨x, hx⟩
    rw [h₀ x] at hx
    by_cases h1 : 4 * x + 1 ≤ x + 2
    · -- Case 1: When 4x + 1 ≤ x + 2, then min (4 * x + 1) (x + 2) = 4 * x + 1
      have h2 : min (4 * x + 1) (x + 2) = 4 * x + 1 := by
        apply min_eq_left
        linarith
      rw [h2] at hx
      by_cases h3 : 4 * x + 1 ≤ -2 * x + 4
      · -- Subcase 1a: If 4x + 1 ≤ -2x + 4, then min (4 * x + 1) (-2 * x + 4) = 4 * x + 1
        have h4 : min (4 * x + 1) (-2 * x + 4) = 4 * x + 1 := by
          apply min_eq_left
          linarith
        rw [h4] at hx
        linarith
      · -- Subcase 1b: If 4x + 1 > -2x + 4, then min (4 * x + 1) (-2 * x + 4) = -2 * x + 4
        have h4 : min (4 * x + 1) (-2 * x + 4) = -2 * x + 4 := by
          apply min_eq_right
          linarith
        rw [h4] at hx
        linarith -- This leads to a contradiction since the interval is inconsistent
    · -- Case 2: When 4x + 1 > x + 2, then min (4 * x + 1) (x + 2) = x + 2
      have h2 : min (4 * x + 1) (x + 2) = x + 2 := by
        apply min_eq_right
        linarith
      rw [h2] at hx
      by_cases h3 : x + 2 ≤ -2 * x + 4
      · -- Subcase 2a: If x + 2 ≤ -2x + 4, then min (x + 2) (-2 * x + 4) = x + 2
        have h4 : min (x + 2) (-2 * x + 4) = x + 2 := by
          apply min_eq_left
          linarith
        rw [h4] at hx
        linarith
      · -- Subcase 2b: If x + 2 > -2x + 4, then min (x + 2) (-2 * x + 4) = -2 * x + 4
        have h4 : min (x + 2) (-2 * x + 4) = -2 * x + 4 := by
          apply min_eq_right
          linarith
        rw [h4] at hx
        linarith