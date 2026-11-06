import Mathlib

theorem calculus_23006 (a b : ℝ × ℝ × ℝ)
    (hb : b = (2, 6, 3)) (h : a • b = 8) :
    (a • b) / (2^2 + 6^2 + 3^2) * b = (16 / 49, 48 / 49, 24 / 49) := by
  rw [h]
  rw [hb]
  simp [Prod.ext_iff]
  all_goals norm_num
  <;> ring