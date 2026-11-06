import Mathlib

theorem algebra_298945 (z : ℂ) (h : ∃ r : ℝ, r^2 - 2 * z * r + 3 / 4 + Complex.I = 0) :
    Complex.abs z ≥ 1 := by
  rcases h with ⟨r, hr⟩
  have eq1 := congr_arg Complex.re hr
  have eq2 := congr_arg Complex.im hr
  simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq1 eq2
  have h1 : (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 ≥ 1 := by
    by_cases him : z.im = 0
    · -- z.im = 0
      have h_eq2 : -2 * (z.im : ℝ) * r + 1 = 0 := by linarith
      rw [him] at h_eq2
      nlinarith
    · -- z.im ≠ 0
      have h_eq2 : -2 * (z.im : ℝ) * r + 1 = 0 := by linarith
      have hr_eq : r = 1 / (2 * z.im) := by
        have : z.im ≠ 0 := him
        field_simp
        nlinarith
      have h_eq1 : r ^ 2 - 2 * (z.re : ℝ) * r + 3 / 4 = 0 := by linarith
      rw [hr_eq] at h_eq1
      have h_eq3 : 3 * z.im ^ 2 - 4 * z.re * z.im + 1 = 0 := by
        field_simp [show (z.im : ℝ) ≠ 0 by exact him] at h_eq1
        nlinarith
      nlinarith [sq_nonneg (z.re - 2 * z.im), sq_nonneg (z.re + 2 * z.im), sq_nonneg (z.im ^ 2 - 1 / 5), sq_nonneg (z.re ^ 2 - 4 / 5),
          sq_nonneg (3 * z.im - 2 * z.re), sq_nonneg (3 * z.im + 2 * z.re), sq_pos_of_ne_zero (show (z.im : ℝ) ≠ 0 by exact him), sq_nonneg (z.re - 2 * z.im), sq_nonneg (z.re + 2 * z.im)]
  have h2 : Complex.abs z = Real.sqrt ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  have h3 : Real.sqrt ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2) ≥ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (show (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 ≥ (1 : ℝ) by linarith [h1])
  have h4 : Real.sqrt (1 : ℝ) = 1 := by
    rw [Real.sqrt_eq_cases]
    norm_num
  linarith [h2, h3, h4]