import Mathlib

theorem algebra_13068 {a b : ℝ} (h : (1 + Real.sqrt 3 * Complex.I)^2 + a * (1 + Real.sqrt 3 * Complex.I) + b = 0) :
    a + b = 2 := by
  simp [Complex.ext_iff, pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, mul_add, add_mul] at h
  ring_nf at h 
  have real_eq : -2 + a + b = 0 := by
    linarith [h.1]
  have imag_eq : 2 * Real.sqrt 3 + a * Real.sqrt 3 = 0 := by
    linarith [h.2]
  have ha : a = -2 := by 
    have h1 : Real.sqrt 3 * (2 + a) = 0 := by 
      linarith 
    have h2 : Real.sqrt 3 ≠ 0 := by 
      positivity 
    have h3 : 2 + a = 0 := by 
      apply (mul_left_inj' h2).mp 
      linarith 
    linarith 
  have hb : b = 4 := by 
    rw [ha] at real_eq 
    linarith 
  linarith [ha, hb]