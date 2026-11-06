import Mathlib

open Real
theorem geometry_97049 (P : ℝ × ℝ) (hP : P = (-3, 2)) :
let B := (P.2, -P.1)
let C := (B.2, B.1)
C = (3, 2) := by
  rw [hP]
  norm_num