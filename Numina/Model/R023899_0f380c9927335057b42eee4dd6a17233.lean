import Mathlib

theorem algebra_10975 (P Q R : ℝ × ℝ)
    (hP : P = (1, 6)) (hQ : Q = (-5, 0)) (hR : R = (-2, 0)) :
    (1/2) * abs (P.1 * (Q.2 - R.2) - Q.1 * (P.2 - R.2) + R.1 * (P.2 - Q.2)) = 9 := by
  rw [hP, hQ, hR]
  norm_num [abs_of_nonneg]
  all_goals norm_num [abs_of_nonneg]