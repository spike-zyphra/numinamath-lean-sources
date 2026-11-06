import Mathlib
open Real
/-What is the sum of the reciprocals of the roots of the equation
2003/2004*x+1+1/x = 0?
(A) -2004/2003 (B) -1  (C) 2003/2004 (D) 1 (E) 2004/2003-/
theorem algebra_94616 {x : ℝ} (hx : x ≠ 0) (h : 2003 / 2004 * x + 1 + 1 / x = 0) :
∃ y:ℝ, 2003/2004 * y + 1 + 1 / y = 0 ∧ 1/x + 1/y = -1 := by
  -- getting rid of the division
  rw [← mul_left_inj' hx] at h
  rw [add_mul,add_mul] at h
  rw [← div_left_inj' ((by norm_num):(2003:ℝ) / 2004 ≠ 0)] at h
  have h':(2003 / 2004 * x * x + 1 * x + 1 / x * x) / (2003 / 2004)=x*x-(-2004/2003)*x+(2004/2003):=by field_simp;ring
  rw [h',zero_mul,zero_div] at h

  -- using the vieta formula to obtain the sum and product of the roots

  obtain ⟨y,hy,hs,hp⟩ := vieta_formula_quadratic h
  obtain ⟨_,hy0⟩:= mul_ne_zero_iff.1 ((by rw [hp];norm_num):x * y ≠ 0)

  -- use y as the witness and prove the required properties
  
  use y
  constructor
  field_simp at hy
  field_simp
  linarith
  field_simp
  linarith