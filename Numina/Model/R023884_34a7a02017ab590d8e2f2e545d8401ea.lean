import Mathlib

theorem algebra_253965 (z : ℂ) : z * (z.re - z.im * .I) + 1 = - .I * (z - (z.re - z.im * .I)) ↔ z = .I := by
  constructor
  · -- Assume z * (z.re - z.im * .I) + 1 = - .I * (z - (z.re - z.im * .I)), prove z = .I
    intro h
    have eq1 := congr_arg Complex.re h
    have eq2 := congr_arg Complex.im h
    simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq1 eq2
    have h1 : z.re ^ 2 + (z.im - 1) ^ 2 = 0 := by
      nlinarith
    have h2 : z.re = 0 := by
      nlinarith [sq_nonneg z.re, sq_nonneg (z.im - 1)]
    have h3 : z.im = 1 := by
      nlinarith [sq_nonneg z.re, sq_nonneg (z.im - 1)]
    simp [Complex.ext_iff, h2, h3]
  · -- Assume z = .I, prove z * (z.re - z.im * .I) + 1 = - .I * (z - (z.re - z.im * .I))
    intro h
    rw [h]
    simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    all_goals norm_num