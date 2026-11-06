import Mathlib

theorem algebra_2145 (x y : ℝ) (h₀ : x + 3 * y + abs (3 * x - y) = 19) (h₁ : 2 * x + y = 6) :
    x = 1 / 2 ∧ y = 5 := by
  have h2 : y = 6 - 2 * x := by 
    linarith 
  rw [h2] at h₀
  have eq1 : x + 3 * (6 - 2 * x) + abs (3 * x - (6 - 2 * x)) = 19 := by 
    linarith [h₀]
  have eq2 : -5 * x + abs (5 * x - 6) = 1 := by
    have h3 : 3 * x - (6 - 2 * x) = 5 * x - 6 := by ring 
    rw [h3] at eq1
    linarith [eq1]
  by_cases h : 5 * x - 6 ≥ 0 
  · -- Case 1: 5 * x - 6 ≥ 0, so |5 * x - 6| = 5 * x - 6
    rw [abs_of_nonneg h] at eq2 
    linarith 
  · -- Case 2: 5 * x - 6 < 0, so |5 * x - 6| = 6 - 5 * x
    rw [abs_of_neg (lt_of_not_ge h)] at eq2 
    have hx : x = 1 / 2 := by
      linarith 
    have hy : y = 5 := by
      rw [hx] at h2 
      linarith 
    constructor 
    · exact hx 
    · exact hy