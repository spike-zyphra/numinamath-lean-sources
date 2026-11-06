import Mathlib

theorem algebra_10876 {x y : ℕ} (hx : x = 3) (hy : y = 7) :
    ((x * y) / 2) * 2 = (21 : ℝ) := by
  have hx' : (x : ℝ) = 3 := by exact_mod_cast hx
  have hy' : (y : ℝ) = 7 := by exact_mod_cast hy
  rw [hx', hy']
  norm_num