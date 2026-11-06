import Mathlib

theorem algebra_173860 {a b : ℝ} (h : (a + Complex.I * b) ^ 2 = 3 + 4 * Complex.I) :
    a ^ 2 + b ^ 2 = 5 := by 
  have eq1 := congr_arg Complex.re h
  have eq2 := congr_arg Complex.im h
  simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq1 eq2
  have h1 : a^2 - b^2 = 3 := by nlinarith
  have h2 : 2 * a * b = 4 := by nlinarith
  have hab : a * b = 2 := by linarith
  have ha : a ≠ 0 := by 
    by_contra h'
    rw [h'] at hab
    nlinarith
  have hb : b = 2 / a := by 
    field_simp [ha]
    nlinarith
  rw [hb] at h1
  have eq3 : a^4 - 3 * a^2 - 4 = 0 := by 
    field_simp [ha] at h1
    nlinarith
  have ha2 : a^2 = 4 := by 
    have h4 : a^2 ≥ 0 := by nlinarith
    nlinarith [sq_nonneg (a^2 - 4), sq_nonneg (a^2 + 1)]
  have hb2 : b^2 = 1 := by 
    rw [hb]
    field_simp [ha]
    nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), ha2]
  nlinarith [ha2, hb2]