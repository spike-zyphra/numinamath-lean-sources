import Mathlib

theorem algebra_13324 : 4 / (Real.sqrt 108 + 2 * Real.sqrt 12 + 2 * Real.sqrt 27) = Real.sqrt 3 / 12 := by
  have h1 : Real.sqrt 108 = 6 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h2 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h3 : Real.sqrt 27 = 3 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  rw [h1, h2, h3]
  have h4 : Real.sqrt 3 > 0 := by positivity
  field_simp [(show 6 * Real.sqrt 3 + 2 * (2 * Real.sqrt 3) + 2 * (3 * Real.sqrt 3) ≠ 0 by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  )]
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num
  <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]