import Mathlib

theorem algebra_154227 {x y : ℝ} (h1 : 3 * y + 5 * x * Complex.I = 15 - 7 * Complex.I)
    (h2 : (2 * x + 3 * y) + (x - y) * Complex.I = 7 + 6 * Complex.I) :
    x = -7 / 5 ∧ y = 5 := by 
  have eq1 := congr_arg Complex.re h1
  have eq2 := congr_arg Complex.im h1
  have eq3 := congr_arg Complex.re h2
  have eq4 := congr_arg Complex.im h2
  simp [Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.ofReal_im, Complex.I_im] at eq1 eq2 eq3 eq4
  have hy : y = 5 := by 
    linarith 
  have hx : x = -7 / 5 := by 
    linarith 
  have h5 : 2 * x + 3 * y = 7 := by 
    linarith [eq3]
  have h6 : x - y = 6 := by 
    linarith [eq4]
  rw [hx, hy] at h5 h6 
  norm_num at h5 h6 
  all_goals 
    constructor
    · linarith 
    · linarith