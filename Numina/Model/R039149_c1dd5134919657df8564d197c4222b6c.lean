import Mathlib

open Matrix

theorem calculus_17188 (a b : ℝ)
    (h : !![3, -8; a, 11]⁻¹ = !![11, b; 4, 3]) :
    a = -4 ∧ b = 8 := by 
  have eq1 := congr_arg (fun x => x 0 0) h 
  have eq2 := congr_arg (fun x => x 0 1) h 
  have eq3 := congr_arg (fun x => x 1 0) h 
  have eq4 := congr_arg (fun x => x 1 1) h 
  simp [Matrix.inv, Matrix.det_fin_two, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] at eq1 eq2 eq3 eq4 
  ring_nf at eq1 eq2 eq3 eq4
  have h11 : a = -4 := by
    nlinarith [sq_nonneg (a + 4), sq_nonneg (b - 8), sq_pos_of_ne_zero (show (8 : ℝ) ≠ 0 by 
      norm_num 
    ) ]
  have h12 : b = 8 := by 
    nlinarith [sq_nonneg (a + 4), sq_nonneg (b - 8), sq_pos_of_ne_zero (show (8 : ℝ) ≠ 0 by 
      norm_num 
    ) ]
  constructor 
  · linarith 
  · linarith