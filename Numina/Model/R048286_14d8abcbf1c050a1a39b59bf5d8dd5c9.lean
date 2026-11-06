import Mathlib

theorem number_theory_259592 {a : ℝ} (ha : a = 1 / 10 ^ 2010) :
    max (max (max (max (3 + a) (3 - a)) (3 * a)) (3 / a)) (a / 3) = 3 / a := by
  rw [ha]
  norm_num [max_eq_right, max_eq_left]