import Mathlib

theorem algebra_162043 (A : ℝ) :
    ∃ x1 x2 : ℂ, x1 ≠ x2 ∧ x1 * (x1 + 1) = A ∧ x2 * (x2 + 1) = A ∧
      x1^4 + 3 * x1^3 + 5 * x1 = x2^4 + 3 * x2^3 + 5 * x2 ↔ A = -7 := by

  use (-1 + 3 * Real.sqrt 3 * Complex.I) / 2, (-1 - 3 * Real.sqrt 3 * Complex.I) / 2
  constructor
  · -- Assume the conditions
    intro h
    rcases h with ⟨h12, h1, h2, h3⟩
    have h12' : A = -7 := by
      simp [Complex.ext_iff, pow_two, pow_zero, Complex.I_mul_I, mul_add, add_mul, pow_three, pow_succ] at h1 h2 h3 ⊢
      ring_nf at h1 h2 h3 ⊢
      norm_num [Real.sqrt_pos.mpr, Real.sqrt_nonneg] at h1 h2 h3 ⊢
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    exact h12'
  · -- Assume A = -7.
    intro h
    rw [show A = -7 by linarith [h]]
    constructor
    · -- Show that x1 ≠ x2
      by_contra h
      have h12' : (-1 + 3 * Real.sqrt 3 * Complex.I) / 2 = (-1 - 3 * Real.sqrt 3 * Complex.I) / 2 := by
        exact h
      have h1 : 3 * Real.sqrt 3 / 2 = -(3 * Real.sqrt 3) / 2 := by
        have h1 := congr_arg Complex.im h12'
        simp [Complex.add_im, Complex.mul_im, Complex.I_im] at h1 ⊢
        linarith
      -- From h1: 3 * ↑√3 / 2 = - (3 * ↑√3) / 2
      -- This implies 3 * √3 = 0.
      have h12'' : 3 * Real.sqrt 3 = 0 := by
        field_simp at h1
        nlinarith
      -- Since 3 ≠ 0, we have √3 = 0.
      have h12''' : Real.sqrt 3 = 0 := by
        nlinarith
      -- This is false, because √3 > 0.
      have h5 : Real.sqrt 3 > 0 := by positivity
      linarith
    constructor
    · -- Show that x1 * (x1 + 1) = A
      simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_add, mul_assoc]
      field_simp
      <;> ring_nf <;> norm_num [Real.sqrt_pos.mpr, Real.sqrt_nonneg]
      <;> ring_nf <;> norm_num
    constructor
    · -- Show that x2 * (x2 + 1) = A
      simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_add, mul_assoc]
      field_simp
      <;> ring_nf <;> norm_num [Real.sqrt_pos.mpr, Real.sqrt_nonneg]
      <;> ring_nf <;> norm_num
    · -- Show that x1^4 + 3 * x1^3 + 5 * x1 = x2^4 + 3 * x2^3 + 5 * x2
      simp [pow_two, pow_three, pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_add, mul_assoc]
      field_simp
      <;> ring_nf <;> norm_num [Real.sqrt_pos.mpr, Real.sqrt_nonneg]
      <;> ring_nf <;> norm_num
      all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 - 0)]