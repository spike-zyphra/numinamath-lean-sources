import Mathlib

theorem algebra_300483 {z : ℂ} (hz : (1 / 2) * (z - 1) = (Real.sqrt 3 / 2) * (1 + z) * Complex.I) :
    z = -1 / 2 + Real.sqrt 3 / 2 * Complex.I := by
  have eq1 := congr_arg Complex.re hz
  have eq2 := congr_arg Complex.im hz
  simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, pow_two, Complex.I_re, Complex.I_im, Complex.ext_iff] at eq1 eq2
  have h1 : z.re = -1 / 2 := by
    nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), sq_nonneg (z.re + 1 / 2), sq_nonneg (z.im - Real.sqrt 3 / 2)
    ]
  have h2 : z.im = Real.sqrt 3 / 2 := by
    nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), sq_nonneg (z.re + 1 / 2), sq_nonneg (z.im - Real.sqrt 3 / 2)
    ]
  simp [Complex.ext_iff, h1, h2]
  all_goals try tauto
  all_goals try nlinarith