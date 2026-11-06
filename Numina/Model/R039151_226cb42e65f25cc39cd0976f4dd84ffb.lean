import Mathlib
open Complex

theorem algebra_98106 (a b : ℂ) (ha : a ≠ 0) (hab₁ : a + b ≠ 0) (hab₂ : (a + b) / a = b / (a + b)) :
    a.im ≠ 0 ∨ b.im ≠ 0 := by 
  have h1 : (a + b) ^ 2 = a * b := by
    field_simp [ha, hab₁] at hab₂ 
    ring_nf at hab₂ ⊢ 
    <;> norm_num [Complex.ext_iff] at hab₂ ⊢ 
    <;> constructor <;> nlinarith 
  by_contra h 
  push_neg at h 
  rcases h with ⟨ha_im, hb_im⟩ 
  have eq1 := congr_arg Complex.re h1 
  have eq2 := congr_arg Complex.im h1
  simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
        ha_im, hb_im] at eq1 eq2 
  have h4 : a.re ^ 2 + a.re * b.re + b.re ^ 2 = 0 := by 
    nlinarith 
  have h5 : a.re ≠ 0 := by 
    by_contra h6 
    have h7 : a = 0 := by 
      simp [Complex.ext_iff, h6, ha_im] 
    contradiction 
  have h7 : a.re ^ 2 + a.re * b.re + b.re ^ 2 > 0 := by 
    nlinarith [sq_pos_of_ne_zero (show a.re ≠ 0 by assumption), sq_nonneg (b.re), sq_nonneg (a.re - b.re), sq_nonneg (a.re + b.re)]
  linarith