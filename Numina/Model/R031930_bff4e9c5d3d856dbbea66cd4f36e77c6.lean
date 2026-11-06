import Mathlib

open Real Set
open scoped Real

theorem algebra_245685 (α : Real) 
    (h1 : cos (α / 2) ≠ 0) 
    (h2 : sin (π / 4 + α / 4) ≠ 0) :
    (1 - sin (α / 2)) / cos (α / 2) = cot (π / 4 + α / 4) := by
  have h3 : cot (π / 4 + α / 4) = cos (π / 4 + α / 4) / sin (π / 4 + α / 4) := by
    rw [cot_eq_cos_div_sin]
  have h4 : cos (π / 4 + α / 4) = Real.sqrt 2 / 2 * (cos (α / 4) - sin (α / 4)) := by
    have h5 : cos (π / 4 + α / 4) = cos (π / 4) * cos (α / 4) - sin (π / 4) * sin (α / 4) := by
      rw [cos_add]
    rw [h5]
    have h7 : cos (π / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    have h8 : sin (π / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    rw [h7, h8]
    ring
  have h5 : sin (π / 4 + α / 4) = Real.sqrt 2 / 2 * (cos (α / 4) + sin (α / 4)) := by
    have h7 : sin (π / 4 + α / 4) = sin (π / 4) * cos (α / 4) + cos (π / 4) * sin (α / 4) := by
      rw [sin_add]
    rw [h7]
    have h7 : cos (π / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    have h8 : sin (π / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    rw [h7, h8]
    ring
  have h6 : sin (α / 2) = 2 * sin (α / 4) * cos (α / 4) := by
    have h7 : sin (α / 2) = 2 * sin (α / 4) * cos (α / 4) := by
      have h7 : sin (2 * (α / 4)) = 2 * sin (α / 4) * cos (α / 4) := by
        rw [sin_two_mul]
      have h8 : 2 * (α / 4) = α / 2 := by ring
      rw [h8] at h7
      linarith
    linarith
  have h7 : cos (α / 2) = cos (α / 4) ^ 2 - sin (α / 4) ^ 2 := by
    have h8 : cos (α / 2) = cos (α / 4) ^ 2 - sin (α / 4) ^ 2 := by
      have h8 : cos (2 * (α / 4)) = cos (α / 4) ^ 2 - sin (α / 4) ^ 2 := by
        rw [cos_two_mul, sin_sq]
        ring
      have h9 : 2 * (α / 4) = α / 2 := by ring
      rw [h9] at h8
      linarith
    linarith
  have h10 : 1 - sin (α / 2) = (cos (α / 4) - sin (α / 4)) ^ 2 := by
    rw [h6]
    have h10 : cos (α / 4) ^ 2 + sin (α / 4) ^ 2 = 1 := Real.cos_sq_add_sin_sq (α / 4)
    nlinarith [h10]
  have h11 : cos (α / 2) = (cos (α / 4) + sin (α / 4)) * (cos (α / 4) - sin (α / 4)) := by
    rw [h7]
    ring_nf
  have h12 : cos (α / 4) + sin (α / 4) ≠ 0 := by
    by_contra h
    have h13 : cos (α / 4) + sin (α / 4) = 0 := by linarith
    have h14 : sin (π / 4 + α / 4) = 0 := by
      rw [h5]
      have h15 : Real.sqrt 2 / 2 * (cos (α / 4) + sin (α / 4)) = 0 := by
        rw [show cos (α / 4) + sin (α / 4) = (0 : ℝ) by linarith [h13]]
        norm_num
      linarith
    contradiction
  have h13 : cos (α / 4) - sin (α / 4) ≠ 0 := by
    by_contra h
    have h14 : cos (α / 4) - sin (α / 4) = 0 := by linarith
    have h15 : cos (α / 2) = 0 := by
      rw [h11]
      rw [show cos (α / 4) - sin (α / 4) = 0 by linarith [h14]]
      norm_num
    contradiction
  rw [h3, h4, h5, h10, h11]
  have h3' : Real.sqrt 2 / 2 ≠ 0 := by
    have h20 : Real.sqrt 2 > 0 := by
      positivity
    linarith
  field_simp [h12, h13, h3']
  <;> ring