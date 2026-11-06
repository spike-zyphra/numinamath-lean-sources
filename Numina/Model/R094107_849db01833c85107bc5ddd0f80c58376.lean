import Mathlib

theorem algebra_16910 {ω : ℂ} (hω : ω = 9 + 2 * .I) :
    Complex.abs (ω ^ 2 + 6 * ω + 58) = 195 := by 
  rw [hω]
  simp [Complex.abs, Complex.normSq, pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num [Real.sqrt_eq_iff_sq_eq] <;> norm_num