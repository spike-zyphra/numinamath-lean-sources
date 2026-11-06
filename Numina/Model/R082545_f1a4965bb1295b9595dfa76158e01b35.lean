import Mathlib

theorem algebra_1554
    (a : ℝ)
    (ha : a = -2) :
    max (max (max (max (-3 * a) (4 * a)) (24 / a)) (a ^ 2)) 1 = 6 := by 
  rw [ha]
  norm_num
  <;> norm_num [max_assoc, max_comm, max_left_comm]