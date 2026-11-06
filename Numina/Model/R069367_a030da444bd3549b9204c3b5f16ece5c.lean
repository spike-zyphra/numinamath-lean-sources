import Mathlib

theorem algebra_21647 (a b : ℝ) (h₀ : a + b = 35) (h₁ : a = 2 / 5 * b) :
    b - a = 15 := by
  have eq1 : b = 25 := by
    linarith [h₀, h₁]
  have eq2 : a = 10 := by
    rw [eq1] at h₁
    linarith
  rw [eq1, eq2]
  all_goals norm_num