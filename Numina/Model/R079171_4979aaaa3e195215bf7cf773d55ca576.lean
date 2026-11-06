import Mathlib

theorem algebra_186614 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a + b + c = 26) (h2 : 1 / a + 1 / b + 1 / c = 28) :
    a / b + b / c + c / a + a / c + c / b + b / a = 725 := by
  have eq1 : a / b + b / c + c / a + a / c + c / b + b / a = (a + b + c) * (1 / a + 1 / b + 1 / c) - 3 := by
    field_simp [ha, hb, hc]
    ring
  rw [eq1, h1, h2]
  norm_num