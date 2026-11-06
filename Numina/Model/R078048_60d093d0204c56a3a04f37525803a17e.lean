import Mathlib

theorem algebra_4641 (m b : ℝ) (h₀ : m * (-2) + b = 3) (h₁ : m * 1 + b = 9) :
    -b / m = -3.5 := by
  have eq1 : m = 2 := by
    linarith
  have eq2 : b = 7 := by
    rw [eq1] at h₀
    linarith
  have h2 : -b / m = -3.5 := by
    rw [eq1, eq2]
    norm_num
  exact h2