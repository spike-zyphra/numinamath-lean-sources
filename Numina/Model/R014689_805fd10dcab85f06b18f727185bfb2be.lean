import Mathlib

theorem algebra_327152 {a b c d e m n : ℝ} (ha : a ≠ 0) (h : a * (m + n * Complex.I)^4 + Complex.I * b * (m + n * Complex.I)^3 + c * (m + n * Complex.I)^2 + Complex.I * d * (m + n * Complex.I) + e = 0) :
    a * (-m + n * Complex.I)^4 + Complex.I * b * (-m + n * Complex.I)^3 + c * (-m + n * Complex.I)^2 + Complex.I * d * (-m + n * Complex.I) + e = 0 := by 
  simp [pow_two, pow_three, pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_add, add_mul] at h ⊢ 
  ring_nf at h ⊢ 
  constructor 
  · -- Real part 
    nlinarith
  · -- Imaginary part 
    nlinarith