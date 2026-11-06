import Mathlib

theorem algebra_301892 {x y : ℝ} (hx : x = (4 * 3 + 2) / 5) (hy : y = (4 * (-9) + 1) / 5) :
    x = 14 / 5 ∧ y = -7 := by 
  constructor
  · -- Show x = 14/5
    rw [hx]
    norm_num
  · -- Show y = -7
    rw [hy]
    norm_num