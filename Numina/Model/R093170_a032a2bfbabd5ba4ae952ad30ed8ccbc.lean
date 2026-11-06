import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_238606 {x : ℝ} (hx : x = 0 ∨ x = -1) :
    arctan (sqrt (x * (x + 1))) + arcsin (sqrt (x * (x + 1) + 1)) = π / 2 := by
  rcases hx with (h | h)
  · -- Case x = 0
    rw [h]
    have h1 : sqrt (0 * (0 + 1 : ℝ)) = 0 := by
      norm_num [sqrt_eq_iff_sq_eq]
      all_goals linarith
    have h2 : sqrt (0 * (0 + 1 : ℝ) + 1) = 1 := by
      norm_num [sqrt_eq_iff_sq_eq]
      all_goals linarith
    rw [h1, h2]
    norm_num
  · -- Case x = -1
    rw [h]
    have h1 : sqrt (-1 * (-1 + 1 : ℝ)) = 0 := by
      norm_num [sqrt_eq_iff_sq_eq]
      all_goals linarith
    have h2 : sqrt (-1 * (-1 + 1 : ℝ) + 1) = 1 := by
      norm_num [sqrt_eq_iff_sq_eq]
      all_goals linarith
    rw [h1, h2]
    norm_num