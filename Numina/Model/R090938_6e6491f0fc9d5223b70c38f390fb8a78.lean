import Mathlib

theorem algebra_298170 {a b c : ℝ} (ha : a = 1.67) (hb : b = 1.71) (hc : c = 0.46) :
    1 / (a^2 - a * c - a * b + b * c) +
    2 / (b^2 - a * b - b * c + a * c) +
    1 / (c^2 - a * c - b * c + a * b) = 20 := by 
  rw [ha, hb, hc]
  norm_num