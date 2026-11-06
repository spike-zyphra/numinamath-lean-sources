import Mathlib
theorem algebra_611087 : 2 * √(1.5 + √2) - (1.5 + √2) = 1 / 2:= by
  have h1 : √(1.5 + √2) = 1 + √2 / 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
  rw [h1]
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]