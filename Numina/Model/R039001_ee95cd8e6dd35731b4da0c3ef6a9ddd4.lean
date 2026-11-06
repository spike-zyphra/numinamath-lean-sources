import Mathlib

open Real Set

theorem algebra_163640 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = min (min (x ^ 2) (6 - x)) (2 * x + 15)) :
    IsGreatest (range f) 9 := by
  constructor
  · -- Show 9 is in the range
    use -3
    norm_num [h₀]
  · -- Show no greater value is in the range
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h₀] at hx
    by_cases h1 : x ^ 2 ≤ 6 - x
    · -- Case 1: x² ≤ 6 - x
      have h2 : min (x ^ 2) (6 - x) = x ^ 2 := by apply min_eq_left h1
      rw [h2] at hx
      by_cases h3 : x ^ 2 ≤ 2 * x + 15
      · -- Case 1a: x² ≤ 2x + 15
        have h4 : min (x ^ 2) (2 * x + 15) = x ^ 2 := by apply min_eq_left h3
        rw [h4] at hx
        nlinarith [sq_nonneg (x + 3)]
      · -- Case 1b: x² > 2x + 15
        have h4 : min (x ^ 2) (2 * x + 15) = 2 * x + 15 := by apply min_eq_right (by nlinarith)
        rw [h4] at hx
        nlinarith [sq_nonneg (x + 3)]
    · -- Case 2: x² > 6 - x
      have h2 : min (x ^ 2) (6 - x) = 6 - x := by apply min_eq_right (by linarith)
      rw [h2] at hx
      by_cases h3 : 6 - x ≤ 2 * x + 15
      · -- Case 2a: 6 - x ≤ 2 x + 15
        have h4 : min (6 - x) (2 * x + 15) = 6 - x := by apply min_eq_left h3
        rw [h4] at hx
        nlinarith [sq_nonneg (x + 3)]
      · -- Case 2b: 6 - x > 2 x + 15
        have h4 : min (6 - x) (2 * x + 15) = 2 * x + 15 := by apply min_eq_right (by linarith)
        rw [h4] at hx
        nlinarith [sq_nonneg (x + 3)]