import Mathlib

theorem algebra_219109 (a b c d : ℝ) (ha : a = 7) (hb : b = 8) (hc : c = 9)
    (hd : d = 3 + 1 / 2 + 1 / 4) :
    a * d / (a + b + c) = 1 + 3 / 32 ∧ b * d / (a + b + c) = 1 + 1 / 4 ∧
    c * d / (a + b + c) = 1 + 13 / 32 := by
  rw [ha, hb, hc, hd]
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num