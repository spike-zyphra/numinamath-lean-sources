import Mathlib

theorem algebra_7112 {α β : ℝ} (a b : ℝ) (h : Complex.exp (Complex.I * α) + Complex.exp (Complex.I * β) = a + b * Complex.I) :
    Complex.exp (-Complex.I * α) + Complex.exp (-Complex.I * β) = a - b * Complex.I := by
  have eq1 := congr_arg Complex.re h
  have eq2 := congr_arg Complex.im h
  -- Assume $b = \operatorname{Im}(z) = \sin \alpha + \sin \beta$
  have eq3 : (Complex.exp (Complex.I * α)).re + (Complex.exp (Complex.I * β)).re = a := by
    simp [Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.zero_re] at eq1 ⊢ 
    linarith
  -- Assume $b = \operatorname{Im}(z) = \sin \alpha + \sin \beta$
  have eq4 : (Complex.exp (Complex.I * α)).im + (Complex.exp (Complex.I * β)).im = b := by
    simp [Complex.add_im, Complex.ofReal_im, Complex.I_im, Complex.zero_im] at eq2 ⊢ 
    linarith
  -- Assume $b = \operatorname{Im}(z) = \sin \alpha + \sin \beta$
  have eq5 : (Complex.exp (Complex.I * α)).re = Real.cos α := by 
    simp [Complex.exp_re, Complex.cos_sq]
  have eq6 : (Complex.exp (Complex.I * α)).im = Real.sin α := by 
    simp [Complex.exp_im, Complex.sin_sq]
  have eq7 : (Complex.exp (Complex.I * β)).re = Real.cos β := by 
    simp [Complex.exp_re, Complex.cos_sq]
  have eq8 : (Complex.exp (Complex.I * β)).im = Real.sin β := by 
    simp [Complex.exp_im, Complex.sin_sq]
  -- Assume $b = \operatorname{Im}(z) = \sin \alpha + \sin \beta$
  have eq9 : Real.cos α + Real.cos β = a := by
    rw [eq5, eq7] at eq3 
    linarith 
  have eq10 : Real.sin α + Real.sin β = b := by 
    rw [eq6, eq8] at eq4
    linarith
  have eq11 : (Complex.exp (-Complex.I * α)).re + (Complex.exp (-Complex.I * β)).re = a := by
    have h9 : (Complex.exp (-Complex.I * α)).re = Real.cos α := by
      simp [Complex.exp_re, Complex.cos_sq, mul_comm]
    have h10 : (Complex.exp (-Complex.I * β)).re = Real.cos β := by
      simp [Complex.exp_re, Complex.cos_sq, mul_comm]
    rw [h9, h10] 
    linarith [eq9]
  have eq12 : (Complex.exp (-Complex.I * α)).im + (Complex.exp (-Complex.I * β)).im = -b := by 
    have h9 : (Complex.exp (-Complex.I * α)).im = -Real.sin α := by 
      simp [Complex.exp_im, Complex.sin_sq, mul_comm]
    have h10 : (Complex.exp (-Complex.I * β)).im = -Real.sin β := by 
      simp [Complex.exp_im, Complex.sin_sq, mul_comm]
    rw [h9, h10] 
    linarith [eq10]
  -- The final step: prove it right
  simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im] at *
  constructor
  · -- Show that the real parts are equal
    have eq13 : (Complex.exp (-Complex.I * α) + Complex.exp (-Complex.I * β)).re = (a - b * Complex.I).re := by
      simp [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.I_re, mul_comm] at *
      <;> linarith [eq11]
    simpa using eq13
  · -- Show that the imaginary parts are equal
    have eq14 : (Complex.exp (-Complex.I * α) + Complex.exp (-Complex.I * β)).im = (a - b * Complex.I).im := by
      simp [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.I_im, mul_comm] at *
      <;> linarith [eq12]
    simpa using eq14