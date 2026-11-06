import Mathlib

theorem algebra_13398 (O : ℝ × ℝ) (hO : O = (2, 3)) (d : ℝ × ℝ) (hd : d = (-1, -1)) :
    (d.1 + 2 * (O.1 - d.1), d.2 + 2 * (O.2 - d.2)) = (5, 7) := by
  rw [hO, hd]
  norm_num