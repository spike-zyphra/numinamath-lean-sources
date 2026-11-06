import Mathlib

theorem algebra_121662
    (a b c1 c2 : ℝ × ℝ × ℝ)
    (ha : a = (5, 0, -1))
    (hb : b = (7, 2, 3))
    (hc1 : c1 = 2 * a - b)
    (hc2 : c2 = 3 * b - 6 * a) :
    c1 = -1 / 3 * c2 := by 
  rw [hc1, hc2, ha, hb]
  simp [Prod.ext_iff, mul_add, mul_sub]
  all_goals norm_num