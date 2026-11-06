import Mathlib

theorem algebra_226751 (a : ℝ) (ha : a ≠ 0) :
    (1 - 1 / a) ^ 6 = 1 + 6 * (-1 / a) + 15 * (1 / a) ^ 2 + 20 * (-1 / a) ^ 3 + 15 * (1 / a) ^ 4 + 6 * (-1 / a) ^ 5 + (1 / a) ^ 6 := by 
  field_simp [ha]
  ring_nf