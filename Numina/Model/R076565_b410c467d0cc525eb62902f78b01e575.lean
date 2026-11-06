import Mathlib

theorem algebra_128008 {x : ℕ} (hx : x ≠ 0) (h1 : (18 / 100 : ℝ) * x + (3 / 100 : ℝ) * x + 84 = x) :
    x = 400 := by
  have h3 : (79 : ℝ) * (x : ℝ) = 8400 := by 
    nlinarith
  have h4 : 79 * (x : ℝ) = 8400 := by
    exact_mod_cast h3
  have h5 : 79 * x = 8400 := by
    exact_mod_cast h4
  omega