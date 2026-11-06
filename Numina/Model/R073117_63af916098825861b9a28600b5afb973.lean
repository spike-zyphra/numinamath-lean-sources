import Mathlib

theorem algebra_4916 (A : ℝ × ℝ) (hA : A = (-3, 11)) (m : ℝ) (hm : m = 9 / 23) :
    (A.1 * m - A.2) / m = -31 - 1 / 9 := by
  rw [hA, hm]
  norm_num