import Mathlib

open Real Set
open scoped Real

theorem algebra_164330 (α : Real) :
  1 - cos (3 * π / 2 - 3 * α) - sin (3 * α / 2) ^ 2 +
  cos (3 * α / 2) ^ 2 =
  2 * sqrt 2 * cos (3 * α / 2) * sin (3 * α / 2 + π / 4) := by
  have h1 : cos (3 * π / 2 - 3 * α) = -sin (3 * α) := by
    have h1 : cos (3 * π / 2 - 3 * α) = -sin (3 * α) := by
      have h2 : 3 * π / 2 - 3 * α = π + (π / 2 - 3 * α) := by 
        linarith [Real.pi_pos]
      rw [h2]
      rw [cos_add]
      rw [cos_pi, sin_pi]
      have h3 : cos (π / 2 - 3 * α) = sin (3 * α) := by 
        rw [cos_pi_div_two_sub]
      have h4 : sin (π / 2 - 3 * α) = cos (3 * α) := by 
        rw [sin_pi_div_two_sub]
      simp [h3, h4]
      all_goals linarith
    exact h1
  have h2 : cos (3 * α / 2) ^ 2 - sin (3 * α / 2) ^ 2 = cos (3 * α) := by 
    have h3 : cos (3 * α) = cos (2 * (3 * α / 2)) := by 
      ring_nf
    rw [h3]
    rw [cos_two_mul]
    rw [sin_sq]
    <;> ring_nf <;> simp [Real.cos_sq, Real.sin_sq]
    <;> ring_nf <;> simp [Real.cos_sq, Real.sin_sq]
  -- The proof of the original identity
  have h3 : (1 - cos (3 * π / 2 - 3 * α) - sin (3 * α / 2) ^ 2 + cos (3 * α / 2) ^ 2) = 1 + sin (3 * α) + cos (3 * α) := by
    rw [h1]
    have h4 : cos (3 * α / 2) ^ 2 - sin (3 * α / 2) ^ 2 = cos (3 * α) := h2
    linarith [h4]
  
  have h4 : 2 * sqrt 2 * cos (3 * α / 2) * sin (3 * α / 2 + π / 4) = 1 + sin (3 * α) + cos (3 * α) := by
    have h5 : sin (3 * α / 2 + π / 4) = sin (3 * α / 2) * cos (π / 4) + cos (3 * α / 2) * sin (π / 4) := by 
      rw [sin_add]
    have h6 : cos (π / 4) = Real.sqrt 2 / 2 := by 
      exact cos_pi_div_four
    have h7 : sin (π / 4) = Real.sqrt 2 / 2 := by 
      exact sin_pi_div_four
    rw [h5, h6, h7]
    have h8 : sin (3 * α) = 2 * sin (3 * α / 2) * cos (3 * α / 2) := by 
      rw [←sin_two_mul]
      ring_nf
    have h14 : 2 * cos (3 * α / 2) ^ 2 = 1 + cos (3 * α) := by 
      have h16 : cos (3 * α) = 2 * cos (3 * α / 2) ^ 2 - 1 := by 
        rw [←cos_two_mul]
        ring_nf
      linarith [h16]
    have h11 : 2 * Real.sqrt 2 * cos (3 * α / 2) * (sin (3 * α / 2) * (Real.sqrt 2 / 2) + cos (3 * α / 2) * (Real.sqrt 2 / 2)) = 
      2 * cos (3 * α / 2) * (sin (3 * α / 2) + cos (3 * α / 2)) := by 
      ring_nf
      <;> 
      simp [Real.sqrt_mul_self, Real.sin_sq_add_cos_sq, mul_add, add_mul]
      <;> ring_nf <;> simp [Real.sin_sq_add_cos_sq]
      <;> ring_nf <;> simp [Real.sin_sq_add_cos_sq]
    have h12 : 2 * cos (3 * α / 2) * (sin (3 * α / 2) + cos (3 * α / 2)) = sin (3 * α) + 1 + cos (3 * α) := by 
      have eq1 : sin (3 * α) = 2 * sin (3 * α / 2) * cos (3 * α / 2) := h8
      have h16 : 2 * sin (3 * α / 2) * cos (3 * α / 2) = sin (3 * α) := by 
        rw [eq1]
      have h18 : 2 * cos (3 * α / 2) * (sin (3 * α / 2) + cos (3 * α / 2)) = 
        2 * sin (3 * α / 2) * cos (3 * α / 2) + 2 * cos (3 * α / 2) ^ 2 := by 
          ring
      have h19 : 2 * cos (3 * α / 2) ^ 2 = 1 + cos (3 * α) := h14
      rw [h18]
      linarith [h16, h19]
    linarith [h11, h12]
  linarith [h3, h4]