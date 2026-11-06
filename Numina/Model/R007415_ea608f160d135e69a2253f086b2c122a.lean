import Mathlib

theorem algebra_10197 (A B : ℝ × ℝ) (hA : A = (-1, 4)) (hB : B = (2, -3)) :
    (B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2 = 58 := by
  rw [hA, hB]
  norm_num