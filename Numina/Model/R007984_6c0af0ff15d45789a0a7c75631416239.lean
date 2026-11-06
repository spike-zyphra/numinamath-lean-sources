import Mathlib


theorem algebra_10554 {z : ℂ} (hz : 1 - Complex.I * z = -1 + Complex.I * z) : z = -Complex.I := by
  have eq1 := congr_arg Complex.re hz
  have eq2 := congr_arg Complex.im hz
  simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq1 eq2
  have hy : z.im = -1 := by 
    linarith 
  have hx : z.re = 0 := by
    linarith 
  rw [Complex.ext_iff]
  simp [hx, hy]
  all_goals linarith