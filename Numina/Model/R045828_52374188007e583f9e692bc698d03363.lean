import Mathlib

open Real Set
open scoped Real

theorem algebra_116483 (x : ℝ) (hx : x ∈ Ioo (-3 * π / 4) (π / 4)) (h : cos (π / 4 - x) = -3 / 5) :
    cos (2 * x) = -24 / 25 := by

  rcases hx with ⟨hx1, hx2⟩

  have h1 : π / 4 - x > 0 := by
    linarith

  have h2 : π / 4 - x < π := by 
    linarith [Real.pi_pos, hx2]

  have h3 : sin (π / 4 - x) ≥ 0 := by
    apply sin_nonneg_of_nonneg_of_le_pi
    · linarith
    · linarith [Real.pi_pos, hx2]

  have h4 : sin (π / 4 - x) = 4 / 5 := by 
    have h5 : sin (π / 4 - x) ^ 2 + cos (π / 4 - x) ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq (π / 4 - x)
    rw [h] at h5
    have h6 : sin (π / 4 - x) ^ 2 = 16 / 25 := by
      nlinarith
    have h7 : sin (π / 4 - x) ≥ 0 := by
      apply sin_nonneg_of_nonneg_of_le_pi
      · linarith
      · linarith [Real.pi_pos, hx2]
    nlinarith [h6, h7]

  have h5 : cos (2 * x) = cos ( (π / 2) - 2 * (π / 4 - x) ) := by 
    ring_nf

  have h6 : cos ( (π / 2) - 2 * (π / 4 - x) ) = sin (2 * (π / 4 - x) ) := by
    rw [cos_pi_div_two_sub]

  have h7 : sin (2 * (π / 4 - x) ) = 2 * sin (π / 4 - x) * cos (π / 4 - x) := by 
    rw [sin_two_mul]

  rw [h5, h6, h7, h4, h]

  norm_num