import Mathlib

theorem algebra_196968 {a : ℝ} (ha : (2002^3 + 4 * 2002^2 + 6006) / (2002^2 + 2002) = a) :
    a = 2005 := by
  have h : a = (2002^3 + 4 * 2002^2 + 6006) / (2002^2 + 2002) := by
    linarith [ha]
  rw [h]
  norm_num