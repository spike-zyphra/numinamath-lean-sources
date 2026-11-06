import Mathlib

theorem algebra_285740 : ∃ n : ℕ, 0 < n ∧ (∃ z : ℂ, z = ((3 - Real.sqrt 3 * .I) / 2)^n ∧ z.re = 0 ∧ z.im ≠ 0) := by
  use 3
  constructor
  · -- Show n is positive
    norm_num
  · -- Let z be the complex number raised to the power n = 3
    use ((3 - Real.sqrt 3 * Complex.I) / 2) ^ 3
    constructor
    · -- Show z = ((3 - Real.sqrt 3 * Complex.I) / 2) ^ 3
      rfl
    constructor
    · -- Show z.re = 0
      simp [pow_three]
      field_simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_add, add_mul]
      ring_nf
      <;> norm_num
    · -- Show z.im ≠ 0
      simp [pow_three]
      field_simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_add, add_mul]
      ring_nf
      <;> norm_num
      all_goals linarith [Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)]