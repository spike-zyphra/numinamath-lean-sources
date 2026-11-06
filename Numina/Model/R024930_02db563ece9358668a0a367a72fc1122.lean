import Mathlib

open Real Complex Polynomial

theorem calculus_22476 (α β : ℝ) (h₁ : exp (I * α) = 3 / 5 + 4 / 5 * I)
    (h₂ : exp (I * β) = -12 / 13 + 5 / 13 * I) :
    Real.cos (α - β) = -16 / 65 := by

  have cα : Real.cos α = 3 / 5 := by
    have eq1 := congr_arg Complex.re h₁
    simp [Complex.exp_re, Complex.ofReal_re, Complex.I_re, Complex.add_re, Complex.mul_re] at eq1 ⊢
    linarith

  have sα : Real.sin α = 4 / 5 := by
    have eq2 := congr_arg Complex.im h₁
    simp [Complex.exp_im, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im] at eq2 ⊢
    linarith

  have cβ : Real.cos β = -12 / 13 := by
    have eq1 := congr_arg Complex.re h₂
    simp [Complex.exp_re, Complex.ofReal_re, Complex.I_re, Complex.add_re, Complex.mul_re] at eq1 ⊢
    linarith

  have sβ : Real.sin β = 5 / 13 := by
    have eq2 := congr_arg Complex.im h₂
    simp [Complex.exp_im, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im] at eq2 ⊢
    linarith

  have h4 : Real.cos (α - β) = Real.cos α * Real.cos β + Real.sin α * Real.sin β := by 
    rw [Real.cos_sub]

  rw [h4, cα, sα, cβ, sβ]
  all_goals norm_num