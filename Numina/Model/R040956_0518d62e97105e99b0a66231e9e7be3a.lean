import Mathlib

theorem algebra_14112 : {z : ℂ | z^2 = -77 - 36 * .I} = {2 - 9 * .I, -2 + 9 * .I} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- First, prove the forward direction: if z^2 = -77 - 36i, then z is one of the two solutions
    intro h
    have eq1 := congr_arg Complex.re h
    have eq2 := congr_arg Complex.im h
    simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq1 eq2
    have h1 : z.re^2 - z.im^2 = -77 := by linarith
    have h2 : 2 * z.re * z.im = -36 := by linarith
    have h3 : z.re * z.im = -18 := by linarith
    have h4 : (z.re - 2) * (z.re + 2) = 0 := by
      nlinarith [sq_nonneg (z.re^2 - 4), sq_nonneg (z.im^2 - 81), sq_nonneg (z.re * z.im + 18), mul_self_nonneg (z.re - 2), mul_self_nonneg (z.im + 9), mul_self_nonneg (z.re + 2), mul_self_nonneg (z.im - 9)]
    cases' (mul_eq_zero.1 h4) with h6 h7
    · -- z.re = 2
      have h8 : z.re = 2 := by linarith
      have h9 : z.im = -9 := by
        nlinarith
      simp [Complex.ext_iff, h8, h9]
    · -- z.re = -2
      have h10 : z.re = -2 := by linarith
      have h11 : z.im = 9 := by
        nlinarith
      simp [Complex.ext_iff, h10, h11]
  · -- Prove the reverse direction: both solutions satisfy z^2 = -77 - 36i
    rintro (h | h)
    · -- z = 2 - 9 * I
      rw [h]
      simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      all_goals norm_num
    · -- z = -2 + 9 * I
      rw [h]
      simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      all_goals norm_num