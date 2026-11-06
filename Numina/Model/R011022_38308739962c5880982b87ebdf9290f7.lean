import Mathlib

theorem algebra_2377 {x y : ℕ} (h1 : (x - 9 : ℝ) = (1 / 5 : ℝ) * (y - 9)) (h2 : x = (1 / 2 : ℝ) * y) : y = 24 := by
  have eq1 : (x : ℝ) = (1 / 2 : ℝ) * (y : ℝ) := by
    simpa using h2
  rw [show (x : ℝ) = (1 / 2 : ℝ) * (y : ℝ) by linarith [eq1]] at h1
  have eq2 : (y : ℝ) = (24 : ℝ) := by
    linarith
  have eq3 : y = 24 := by
    exact_mod_cast eq2
  exact_mod_cast eq3