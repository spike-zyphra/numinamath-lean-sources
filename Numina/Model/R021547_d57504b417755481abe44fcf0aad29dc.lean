import Mathlib

open Real Set
open scoped Real

theorem algebra_189147 : sin (18 * π / 180) = (sqrt 5 - 1) / 4 := by
  have h2 : sin (18 * π / 180) = sin (π / 10) := by 
    ring_nf
  rw [h2]
  have h4 : cos (π / 5) = (sqrt 5 + 1) / 4 := by 
    have h7 : cos (π / 5) = (1 + sqrt 5) / 4 := by 
      rw [cos_pi_div_five]
      <;> ring_nf <;> field_simp
      <;> ring
    linarith
  have h8 : sin (π / 10) ^ 2 = (1 - cos (π / 5)) / 2 := by
    have h9 : sin (π / 10) ^ 2 = (1 - cos (2 * (π / 10)) ) / 2 := by
      rw [sin_sq_eq_half_sub]
      ring_nf
    have h10 : 2 * (π / 10) = π / 5 := by
      ring_nf
    rw [h10] at h9
    linarith
  have h9 : sin (π / 10) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [pi_pos]
    linarith [pi_pos]
  have h10 : sin (π / 10) = Real.sqrt ((1 - cos (π / 5)) / 2) := by
    have h11 : sin (π / 10) ^ 2 = (1 - cos (π / 5)) / 2 := h8
    have h12 : sin (π / 10) = Real.sqrt (sin (π / 10) ^ 2) := by
      rw [Real.sqrt_sq (show 0 ≤ sin (π / 10) by linarith [h9] ) ]
    rw [h12, h11]
  have h11 : Real.sqrt ((1 - cos (π / 5)) / 2) = (sqrt 5 - 1) / 4 := by
    rw [h4]
    have h12 : Real.sqrt ((1 - (sqrt 5 + 1) / 4) / 2) = (sqrt 5 - 1) / 4 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg ((1 - (sqrt 5 + 1) / 4) / 2), Real.sqrt_nonneg (5 : ℝ), sq_nonneg (sqrt 5 - 1), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_pos_of_pos (show 0 < Real.sqrt 5 by positivity) ]
    linarith [h12]
  rw [h10, h11]
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num