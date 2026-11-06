import Mathlib

open Real Set
open scoped Real

theorem algebra_186196 (α : ℝ) (h : tan α = 2 / 3) :
    sin (2 * α + 5 / 4 * π) = -17 * sqrt 2 / 26 := by
  -- Let's express sin α and cos α in terms of tan α.
  have h1 : cos α ≠ 0 := by
    by_contra h2
    have : tan α = 0 := by
      rw [tan_eq_sin_div_cos]
      rw [h2]
      norm_num
    rw [this] at h
    norm_num at h

  have h2 : sin α = 2 / 3 * cos α := by 
    have htan : tan α = 2 / 3 := h
    have h8 : sin α / cos α = 2 / 3 := by 
      rw [tan_eq_sin_div_cos] at htan
      linarith [htan]
    
    -- Multiply both sides by cos α to get sin α
    have : sin α = 2 / 3 * cos α := by
      have h8' : cos α ≠ 0 := h1
      field_simp [h8'] at h8 ⊢
      <;> nlinarith [h8, Real.sin_sq_add_cos_sq α]

    assumption

  -- Use Pythagorean identity to get the value
  have h3 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  
  -- Solve for cos^2 α using the given condition
  have h6 : cos α ^ 2 = 9 / 13 := by
    have h4 : sin α ^ 2 = 4 / 9 * cos α ^ 2 := by
      rw [h2]
      nlinarith
    nlinarith [h3, h4]

  -- First angle identity: sin(2α + 5/4 * π) = sin(2α + π/4 + π)
  have h7 : sin (2 * α + 5 / 4 * π) = - sin (2 * α + π / 4) := by
    have h10 : sin (2 * α + 5 / 4 * π) = sin ((2 * α + π / 4) + π) := by
      ring_nf
    have h11 : sin ((2 * α + π / 4) + π) = - sin (2 * α + π / 4) := by
      rw [Real.sin_add_pi]
    rw [h10, h11]

  -- Second angle identity: sin(2α + π/4) = sin(2α)cos(π/4) + cos(2α)sin(π/4)
  have h8 : sin (2 * α + π / 4) = sin (2 * α) * cos (π / 4) + cos (2 * α) * sin (π / 4) := by
    rw [Real.sin_add]

  -- Compute sin(2α) and cos(2α)
  have h9 : sin (2 * α) = 2 * sin α * cos α := Real.sin_two_mul α
  have h10 : cos (2 * α) = 2 * cos α ^ 2 - 1 := Real.cos_two_mul α
  -- Calculate sin(2α) * cos(π/4) + cos(2α) * sin(π/4)
  have h11 : sin (π / 4) = sqrt 2 / 2 := Real.sin_pi_div_four
  have h12 : cos (π / 4) = sqrt 2 / 2 := Real.cos_pi_div_four
  
  have h13 : sin (2 * α) = 12 / 13 := by
    have h32 : sin α * cos α = 6 / 13 := by
      nlinarith [h2, h6, Real.sin_sq_add_cos_sq α]
    calc
      sin (2 * α) = 2 * sin α * cos α := by
          rw [h9]
          <;> nlinarith
      _ = 2 * (sin α * cos α) := by ring_nf
      _ = 2 * (6 / 13) := by
          rw [h32]
          <;> nlinarith [Real.sin_sq_add_cos_sq α, h6, h2]
      _ = 12 / 13 := by ring_nf

  have h14 : cos (2 * α) = 5 / 13 := by
    rw [h10]
    nlinarith [h6, Real.sin_sq_add_cos_sq α, h2]

  rw [h7, h8, h13, h14, h11, h12]
  <;> field_simp
  <;> ring_nf
  <;> nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq (2 * α), Real.sin_sq_add_cos_sq (π / 4)]