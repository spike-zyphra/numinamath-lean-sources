import Mathlib

theorem algebra_10690 {f w p : ℂ} (hf : f = 5) (hw : w = 5 + 125 * .I) (h : f * p - w = 10000) :
    p = 2001 + 25 * .I := by 
  rw [hf] at h
  rw [hw] at h
  have eq1 := congr_arg Complex.re h
  have eq2 := congr_arg Complex.im h
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_add, mul_comm] at eq1 eq2 
  have eq3 : p.re = 2001 := by
    linarith 
  have eq4 : p.im = 25 := by 
    linarith 
  rw [Complex.ext_iff]
  simp [eq3, eq4]
  all_goals linarith