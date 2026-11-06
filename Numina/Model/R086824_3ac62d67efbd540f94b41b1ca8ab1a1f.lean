import Mathlib

open Real

theorem other_67506 {p : ℝ} (hp : p = 1 / 2) :
    (1 + 2 * (1 - p)) / p = 4 := by 
  rw [hp]
  norm_num