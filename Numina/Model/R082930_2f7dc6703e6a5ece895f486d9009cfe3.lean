import Mathlib

theorem algebra_170371 {x : ℕ} (hx : x ≠ 0) (h : (60 / 100 : ℝ) * x + (30 / 100 : ℝ) * x + (10 / 100 : ℝ) * x = x) (h1 : (120 / 100 : ℝ) * (30 / 100 : ℝ) * x = (30 / 100 : ℝ) * (60 / 100 : ℝ) * x) (h2 : (30 / 100 : ℝ) * (60 / 100 : ℝ) * x ≤ 150) :
    x = 180 := by
  have eq1 : (x : ℝ) ≠ 0 := by
    exact_mod_cast hx
  have h_zero : (x : ℝ) = 0 := by
    linarith 
  have h_zero_nat : x = 0 := by 
    exact_mod_cast h_zero 
  contradiction 
  all_goals linarith