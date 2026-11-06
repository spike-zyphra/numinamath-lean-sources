import Mathlib

theorem algebra_14171 (A B C : ℝ × ℝ)
    (hA : A = (0, 1)) (hB : B = (4, 0)) (hC : C = (2, 5)) :
    (1 / 2) * abs (A.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2)) = 9 := by
  rw [hA, hB, hC]
  norm_num [abs_of_nonneg]