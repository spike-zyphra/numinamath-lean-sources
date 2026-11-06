import Mathlib

theorem algebra_21164 {n : ℕ} (hn : n ≠ 0) (h : (2 / 3 : ℚ) * n = 834) :
    n = 1251 := by 
  have hn_eq : (n : ℚ) = 834 * (3 / 2 : ℚ) := by
    linarith
  norm_num at hn_eq
  have hn_nat : n = 1251 := by
    exact_mod_cast hn_eq
  exact hn_nat