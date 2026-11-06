import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_10804 {x y : ℝ} (h : sqrt ((x - 3)^2 + (y + 4)^2) + sqrt ((x + 5)^2 + (y - 8)^2) = 20) :
    sqrt ((-5 - 3)^2 + (8 - (-4))^2) = 4 * sqrt 13 := by
  have h1 : sqrt ((-5 - 3)^2 + (8 - (-4))^2) = sqrt 208 := by
    norm_num
  rw [h1]
  have h2 : sqrt 208 = 4 * sqrt 13 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h2]
  all_goals norm_num