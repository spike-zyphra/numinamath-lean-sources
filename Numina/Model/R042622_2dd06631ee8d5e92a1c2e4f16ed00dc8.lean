import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_13939 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = min (min (2 * x + 2) (1 / 2 * x + 1)) (-3 / 4 * x + 7)) :
  IsGreatest (range f) (17 / 5) := by
  constructor
  · -- Show that 17/5 is achievable, at x = 24/5
    use 24 / 5
    rw [h₀]
    norm_num
  · -- Show that 17/5 is indeed the greatest value in the range
    intro y
    rintro ⟨x, hx⟩
    rw [h₀] at hx
    by_cases h1 : 2 * x + 2 ≤ 1 / 2 * x + 1
    · -- Case where $2x + 2 \leq \frac{1}{2}x + 1$
      have h2 : min (2 * x + 2) (1 / 2 * x + 1) = 2 * x + 2 := by
        apply min_eq_left
        linarith
      rw [h2] at hx
      by_cases h2 : 2 * x + 2 ≤ -3 / 4 * x + 7
      · -- Case where $2x + 2 \leq -3/4 x + 7$
        have h3 : min (2 * x + 2) (-3 / 4 * x + 7) = 2 * x + 2 := by
          apply min_eq_left
          linarith
        rw [h3] at hx
        linarith
      · -- Case where $2x + 2 > -3/4 x + 7$
        have h3 : min (2 * x + 2) (-3 / 4 * x + 7) = -3 / 4 * x + 7 := by
          apply min_eq_right
          linarith
        rw [h3] at hx
        linarith
    · -- Case where $2x + 2 > \frac{1}{2}x + 1$
      have h2 : min (2 * x + 2) (1 / 2 * x + 1) = 1 / 2 * x + 1 := by
        apply min_eq_right
        linarith
      rw [h2] at hx
      by_cases h2 : (1 / 2 * x + 1) ≤ (-3 / 4 * x + 7)
      · -- Case where $1/2 * x + 1 \leq -3/4 * x + 7$
        have h3 : min (1 / 2 * x + 1) (-3 / 4 * x + 7) = 1 / 2 * x + 1 := by
          apply min_eq_left
          linarith
        rw [h3] at hx
        linarith
      · -- Case where $1/2 * x + 1 > -3/4 * x + 7$
        have h3 : min (1 / 2 * x + 1) (-3 / 4 * x + 7) = -3 / 4 * x + 7 := by
          apply min_eq_right
          linarith
        rw [h3] at hx
        linarith