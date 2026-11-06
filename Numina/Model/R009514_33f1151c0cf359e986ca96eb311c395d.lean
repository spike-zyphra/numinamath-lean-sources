import Mathlib

theorem algebra_11567 {z : ℂ} (hz : z = 3 + 4 * .I) : z ^ 2 = -7 + 24 * .I := by
  rw [hz]
  simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  all_goals norm_num