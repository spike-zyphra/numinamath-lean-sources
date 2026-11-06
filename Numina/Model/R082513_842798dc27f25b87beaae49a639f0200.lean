import Mathlib

theorem algebra_22150 (ω : ℂ) (hω : ω = 1 - 5 * .I) :
    Complex.abs (2 * ω^2 - 4 * ω - 30) = 82 := by
  rw [hω]
  simp [Complex.abs, Complex.normSq, pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  all_goals norm_num [Real.sqrt_eq_iff_sq_eq] <;> norm_num