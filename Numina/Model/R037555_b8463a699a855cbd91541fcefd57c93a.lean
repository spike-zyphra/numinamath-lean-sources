import Mathlib

theorem algebra_328454 {a b : ℝ} (ha : a ≠ 0) (h : (a + 4 * Complex.I) / (a + 4 * Complex.I + b) = 4 * Complex.I) :
    b = 17 := by 
  have h1 : a + 4 * Complex.I + b ≠ 0 := by 
    by_contra h2
    rw [h2] at h
    field_simp [Complex.ext_iff] at h 
    all_goals norm_num at h <;> nlinarith
  
  have h3 : (a + 4 * Complex.I) = 4 * Complex.I * (a + 4 * Complex.I + b) := by 
    field_simp [h1] at h 
    simpa using h
  
  have eq3 := congr_arg (fun x => x.re) h3
  have eq4 := congr_arg (fun x => x.im) h3
  
  simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq3 eq4
  
  have h4 : a = -16 := by 
    nlinarith
  
  have h5 : b = 17 := by 
    rw [h4] at eq4 
    nlinarith
  
  linarith