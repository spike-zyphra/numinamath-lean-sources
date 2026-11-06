import Mathlib

theorem algebra_267692 (P : ℝ × ℝ) (hP : P = (0, 3)) :
    (P.1 + 2) * (5 - 1) = (P.2 - 1) * (2 + 2) := by 
  rw [hP]
  norm_num