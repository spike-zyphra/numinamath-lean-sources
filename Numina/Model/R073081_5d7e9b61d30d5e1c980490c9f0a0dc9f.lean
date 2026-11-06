import Mathlib

open Real

theorem algebra_284546 : sin (π / 6) ^ 2 + tan (π / 6) * tan (2 * π / 3) + sin (2 * π / 3) ^ 2 = 0 := by

  have h1 : sin (π / 6) = 1 / 2 := by
    rw [sin_pi_div_six]
  have h2 : cos (π / 6) = √3 / 2 := by
    rw [cos_pi_div_six]
  have tan1 : tan (π / 6) = √3 / 3 := by
    rw [tan_eq_sin_div_cos, h1, h2]
    field_simp
    <;> ring_nf <;> norm_num
    <;> ring
  have h3 : sin (2 * π / 3) = √3 / 2 := by
    have h4 : sin (2 * π / 3) = sin (π - (π / 3)) := by ring_nf
    rw [h4]
    rw [sin_pi_sub]
    rw [sin_pi_div_three]
    <;> ring
  have h5 : sin (2 * π / 3) ^ 2 = 3 / 4 := by
    rw [h3]
    have h6 : (√3 / 2) ^ 2 = 3 / 4 := by
      calc
        (√3 / 2) ^ 2 = (√3 ^ 2) / 4 := by ring
        _ = 3 / 4 := by rw [Real.sq_sqrt]; all_goals linarith
    linarith
  have tan2 : tan (2 * π / 3) = -√3 := by
    have h7 : tan (2 * π / 3) = tan (π - (π / 3)) := by ring_nf
    rw [h7]
    rw [tan_pi_sub]
    have h8 : tan (π / 3) = √3 := by
      rw [tan_pi_div_three]
    rw [h8]
    all_goals ring
    <;> norm_num
    <;> ring
  rw [h1, tan1, tan2, h5]
  nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  <;> norm_num
  <;> ring_nf <;> norm_num