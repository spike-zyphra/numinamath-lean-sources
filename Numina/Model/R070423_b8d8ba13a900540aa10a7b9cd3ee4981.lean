import Mathlib

open Real Set
open scoped Real

theorem algebra_147231 (x : ℝ) (hx : sin x ≠ 0) :
    ((1 + cos x) / sin x) ^ 2 + 1 = 2 * (cos x + 1) / sin x ^ 2 := by
  field_simp [hx]
  <;> nlinarith [Real.sin_sq_add_cos_sq x]