import Mathlib

theorem algebra_165353 {x y : ℝ} (h : x + y = 25) (h1 : x = 49 * y) :
    x = 24.5 ∧ y = 0.5 := by 
  have eq1 : y = (1 : ℝ) / 2 := by
    linarith
  have eq2 : x = (49 : ℝ) / 2 := by 
    rw [eq1] at h1
    linarith
  constructor
  · -- Show that x = 24.5
    rw [eq2]
    norm_num
  · -- Show that y = 0.5
    rw [eq1]
    norm_num