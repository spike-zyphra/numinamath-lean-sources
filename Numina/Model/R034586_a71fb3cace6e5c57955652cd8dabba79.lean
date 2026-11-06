import Mathlib

theorem algebra_243492 {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x - y - (1 : ℚ) / x + (1 : ℚ) / y = 0) :
    (x / y : ℝ) ^ 2018 + (y / x : ℝ) ^ 2018 = 2 := by
  have eq1 : (x : ℚ) - (y : ℚ) - (1 : ℚ) / (x : ℚ) + (1 : ℚ) / (y : ℚ) = 0 := by
    simpa using h
  have eq2 : (x : ℚ) = (y : ℚ) := by
    field_simp at eq1
    nlinarith [sq_pos_of_pos (show (x : ℚ) > 0 by positivity), sq_pos_of_pos (show (y : ℚ) > 0 by positivity), mul_pos (show (x : ℚ) > 0 by positivity) (show (y : ℚ) > 0 by positivity)]
  have h_eq : x = y := by
    exact_mod_cast eq2
  have h_eq1 : (x : ℝ) = (y : ℝ) := by
    exact_mod_cast h_eq
  have h1 : (x / y : ℝ) = 1 := by
    have h2 : (y : ℝ) = (x : ℝ) := by linarith [h_eq1]
    have h3 : (x : ℝ) ≠ 0 := by exact_mod_cast hx
    have h4 : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    rw [show (y : ℝ) = (x : ℝ) by linarith [h_eq1]]
    field_simp [show (x : ℝ) ≠ 0 by exact_mod_cast hx]
  have h2 : (y / x : ℝ) = 1 := by
    have h3 : (x : ℝ) = (y : ℝ) := by linarith [h_eq1]
    have h4 : (x : ℝ) ≠ 0 := by exact_mod_cast hx
    have h5 : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    rw [show (x : ℝ) = (y : ℝ) by linarith [h_eq1]]
    field_simp [show (y : ℝ) ≠ 0 by exact_mod_cast hy]
  rw [h1, h2]
  norm_num