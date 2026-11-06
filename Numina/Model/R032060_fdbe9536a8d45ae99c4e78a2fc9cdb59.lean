import Mathlib

open Real Set
open scoped Real

theorem algebra_179359 :
  ¬ ∃ x : ℝ, (arcsin x)^2 + (arccos x)^2 = 1 := by
  rintro ⟨x, hx⟩
  have h1 : arccos x = Real.pi / 2 - arcsin x := by 
    rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  rw [h1] at hx
  have h2 : arcsin x ≤ Real.pi / 2 := by
    linarith [Real.arcsin_le_pi_div_two x]
  have h3 : arcsin x ≥ - Real.pi / 2 := by
    linarith [Real.neg_pi_div_two_le_arcsin x]
  nlinarith [sq_nonneg (arcsin x - Real.pi / 4), sq_nonneg (arcsin x + Real.pi / 4), Real.pi_gt_three, Real.pi_pos, sq_nonneg (arcsin x - Real.pi / 2), sq_nonneg (arcsin x + Real.pi / 2), Real.pi_gt_three, Real.pi_pos, Real.pi_lt_31416]