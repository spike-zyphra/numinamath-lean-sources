import Mathlib

theorem algebra_3713 (a : ℝ) (ha : a > 0) (h : 3 * a * 15 = 350) :
    2 * a * x = 700 ↔ x = 45 := by
  have ha_eq : a = 70 / 9 := by
    nlinarith
  rw [ha_eq]
  constructor
  · -- Assume 2 * (70/9) * x = 700, prove x = 45
    intro h_eq
    linarith
  · -- Assume x = 45, prove 2 * (70/9) * x = 700
    intro h_eq
    rw [h_eq]
    norm_num