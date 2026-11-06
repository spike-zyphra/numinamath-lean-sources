import Mathlib

open Real Set
open scoped Real

theorem algebra_290371 : tan (π / 12) + cot (π / 12) = 4 := by
  have h1 : sin (π / 12) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h2 : cos (π / 12) > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have htan : tan (π / 12) = sin (π / 12) / cos (π / 12) := by
    rw [tan_eq_sin_div_cos]
  have hcot : cot (π / 12) = cos (π / 12) / sin (π / 12) := by
    rw [cot_eq_cos_div_sin]
  rw [htan, hcot]
  have eq1 : sin (2 * (π / 12)) = 2 * sin (π / 12) * cos (π / 12) := by
    rw [sin_two_mul]
  have h5 : sin (2 * (π / 12)) = 1 / 2 := by 
    have h6 : 2 * (π / 12) = π / 6 := by 
      ring_nf
    rw [h6]
    exact sin_pi_div_six
  have eq2 : sin (π / 12) * cos (π / 12) = 1 / 4 := by
    nlinarith
  have h4 : sin (π / 12) ^ 2 + cos (π / 12) ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq (π / 12)
  field_simp [(show sin (π / 12) ≠ 0 by linarith ), (show cos (π / 12) ≠ 0 by linarith ) ]
  nlinarith [sq_nonneg (sin (π / 12) - cos (π / 12)), sq_nonneg (sin (π / 12) * cos (π / 12) - 1 / 4)]