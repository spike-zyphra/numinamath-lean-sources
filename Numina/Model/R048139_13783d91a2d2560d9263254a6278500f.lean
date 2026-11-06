import Mathlib

open Real

theorem algebra_181133 {A : ℝ} (hA : A = 1/2 + 1/3 + 1/4 + 1/5 + 1/6 + 1/7 + 1/8) :
    ⌊A⌋ = 1 := by
  rw [hA]
  norm_num [Int.floor_eq_iff]