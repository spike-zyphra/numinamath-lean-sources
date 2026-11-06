import Mathlib

theorem algebra_266050 (x y z : ℤ) (hx : x = 4) (hy : y = 3 * x) (hz : z = 2 * y) : y + z = 36 := by
  rw [hx] at hy
  have hy' : y = 12 := by 
    linarith
  rw [hy'] at hz
  have hz' : z = 24 := by 
    linarith
  rw [hy', hz']
  all_goals
    norm_num