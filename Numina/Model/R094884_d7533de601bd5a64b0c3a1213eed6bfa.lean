import Mathlib

theorem algebra_20927 (ω : ℂ) (hω : ω = -1 + 4 * .I) : Complex.abs (ω ^ 2 + 2 * ω - 8) = 25 := by
  rw [hω]
  simp [Complex.abs, Complex.normSq, pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring_nf
  norm_num [Real.sqrt_eq_iff_sq_eq]