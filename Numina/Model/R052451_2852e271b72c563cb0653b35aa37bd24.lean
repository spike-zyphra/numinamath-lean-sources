import Mathlib

theorem algebra_133085 (a b c1 c2 : ℝ × ℝ × ℝ)
    (ha : a = (-1, 4, 2))
    (hb : b = (3, -2, 6))
    (hc1 : c1 = 2 * a - b)
    (hc2 : c2 = 3 * b - 6 * a) :
    c1 = -1 / 3 * c2 := by
  rw [hc1, hc2, ha, hb]
  simp [Prod.ext_iff]
  all_goals norm_num