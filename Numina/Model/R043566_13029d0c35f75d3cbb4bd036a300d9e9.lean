import Mathlib

open Complex

theorem algebra_609219 (a b c : ℂ) (h₁ : a ^ 2 + a * b + b ^ 2 = 1 + I) (h₂ : b ^ 2 + b * c + c ^ 2 = -2) (h₃ : c ^ 2 + c * a + a ^ 2 = 1) :
    (a * b + b * c + c * a) ^ 2 = (-11 - 4 * I) / 3 := by

  have eq1 := congr_arg (fun z => z.re) h₁
  have eq2 := congr_arg (fun z => z.im) h₁
  have eq3 := congr_arg (fun z => z.re) h₂
  have eq4 := congr_arg (fun z => z.im) h₂
  have eq5 := congr_arg (fun z => z.re) h₃
  have eq6 := congr_arg (fun z => z.im) h₃

  simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
         Complex.ofReal_re, Complex.ofReal_im] at eq1 eq2 eq3 eq4 eq5 eq6

  simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
        Complex.ofReal_re, Complex.ofReal_im]
  ring_nf at eq1 eq2 eq3 eq4 eq5 eq6 ⊢
  norm_num at eq1 eq2 eq3 eq4 eq5 eq6 ⊢
  constructor
  · nlinarith
  · nlinarith