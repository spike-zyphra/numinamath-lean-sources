import Mathlib

theorem algebra_2333 : (2 + Complex.I)^3 = 2 + 11 * Complex.I := by
  simp [pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  all_goals norm_num