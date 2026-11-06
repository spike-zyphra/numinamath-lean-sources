import Mathlib

theorem calculus_67515 (m : ℝ) (hm : m = 50.0) (r : ℝ) (hr : r = 2.0) (a : ℝ)
    (ha : a = 5.0) :
    (m * r ^ 2) * a = 1000 := by
  rw [hm, hr, ha]
  norm_num