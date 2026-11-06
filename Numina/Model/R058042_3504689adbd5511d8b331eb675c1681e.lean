import Mathlib

theorem inequalities_135508 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a > b) (n : ℕ) (hn : 0 < n) :
    a ^ n > b ^ n := by 
  have h1 : b ^ n < a ^ n := by
    apply pow_lt_pow_left
    all_goals linarith
  linarith