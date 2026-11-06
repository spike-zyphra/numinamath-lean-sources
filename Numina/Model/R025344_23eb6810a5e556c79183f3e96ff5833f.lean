import Mathlib

theorem algebra_22402 (w : ℂ) (h : Complex.abs (3 - 2 * Complex.I + w) = 0) : w = -3 + 2 * Complex.I := by 
  have h1 : Complex.abs (3 - 2 * Complex.I + w) = Real.sqrt (Complex.normSq (3 - 2 * Complex.I + w)) := by
    simp [Complex.abs]
  rw [h1] at h
  have h4 : Real.sqrt (Complex.normSq (3 - 2 * Complex.I + w)) = 0 := h
  have h5 : Complex.normSq (3 - 2 * Complex.I + w) = 0 := by
    have eq5 : Real.sqrt (Complex.normSq (3 - 2 * Complex.I + w)) = 0 := h4
    have eq2 : Complex.normSq (3 - 2 * Complex.I + w) = (3 + w.re) ^ 2 + (-2 + w.im) ^ 2 := by
      simp [Complex.normSq, Complex.add_re, Complex.add_im, pow_two, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    have eq3 : Complex.normSq (3 - 2 * Complex.I + w) ≥ 0 := by
      rw [eq2]
      positivity
    rw [Real.sqrt_eq_zero (by linarith)] at eq5
    all_goals linarith
  have h6 : Complex.normSq (3 - 2 * Complex.I + w) = (3 + w.re) ^ 2 + (-2 + w.im) ^ 2 := by
    simp [Complex.normSq, Complex.add_re, Complex.add_im, pow_two, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    all_goals ring_nf 
    <;> ring
  rw [h6] at h5
  have h7 : w.re = -3 := by
    have h8 : (3 + w.re) ^ 2 = 0 := by
      nlinarith
    have h8'2 : 3 + w.re = 0 := by
      rw [sq_eq_zero_iff] at h8
      linarith
    linarith
  have h8 : w.im = 2 := by
    have h10 : (-2 + w.im) ^ 2 = 0 := by 
      nlinarith
    have h11 : -2 + w.im = 0 := by
      rw [sq_eq_zero_iff] at h10
      linarith
    linarith
  simp [Complex.ext_iff, h7, h8]