import Mathlib

theorem algebra_10235 : (3 - 2 * .I : ℂ) ^ 2 = 5 - 12 * .I := by
  simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  all_goals norm_num