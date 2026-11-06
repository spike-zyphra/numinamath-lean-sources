import Mathlib

theorem algebra_15289 {x y z : ℕ} (hx : x * 25 = 1000) (hy : y * 5 = 1000) (hz : z * 1 = 1000) :
    (x : ℝ) / (x + y + z) = 1 / 31 := by
  have hx' : x = 40 := by
    omega
  have hy' : y = 200 := by
    omega
  have hz' : z = 1000 := by
    omega
  rw [hx', hy', hz']
  norm_num