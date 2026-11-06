import Mathlib

open Real Set
open scoped Real

theorem algebra_162478 (α : Real) :
  1 + sin (3 * (α + π / 2)) * cos (2 * α) +
      2 * sin (3 * α) * cos (3 * π - α) * sin (α - π) =
  2 * sin (5 * α / 2) ^ 2 := by
  have h1 : sin (3 * (α + π / 2)) = - cos (3 * α) := by
    have h2 : 3 * (α + π / 2) = 3 * α + 3 * (π / 2) := by ring
    rw [h2]
    have h3 : sin (3 * α + 3 * (π / 2)) = - cos (3 * α) := by
      have h4 : 3 * α + 3 * (π / 2) = (3 * α + π / 2) + π := by ring
      rw [h4]
      have h5 : sin ((3 * α + π / 2) + π) = - sin (3 * α + π / 2) := by
        rw [sin_add_pi]
      rw [h5]
      have h6 : sin (3 * α + π / 2) = cos (3 * α) := by
        have h7 : sin (3 * α + π / 2) = cos (3 * α) := by
          rw [sin_add_pi_div_two]
        linarith
      linarith
    linarith
  have h2 : cos (3 * π - α) = - cos α := by
    have h3 : cos (3 * π - α) = cos (3 * π) * cos α + sin (3 * π) * sin α := by
      rw [cos_sub]
    have h4 : cos (3 * π) = -1 := by
      have h5 : cos (3 * π) = cos (π + 2 * π) := by ring_nf
      rw [h5]
      have h6 : cos (π + 2 * π) = cos π := by
        rw [cos_add_two_pi]
      rw [h6]
      norm_num
    have h5 : sin (3 * π) = 0 := by
      have h6 : sin (3 * π) = sin (π + 2 * π) := by ring_nf
      rw [h6]
      have h7 : sin (π + 2 * π) = sin π := by
        rw [sin_add_two_pi]
      rw [h7]
      norm_num
    rw [h4, h5] at h3
    linarith [h3]
  have h3 : sin (α - π) = - sin α := by
    have h4 : sin (α - π) = sin α * cos π - cos α * sin π := by
      rw [sin_sub]
    have h5 : cos π = -1 := by
      norm_num
    have h6 : sin π = (0 : ℝ) := by
      norm_num
    rw [h5, h6] at h4
    linarith [h4]
  rw [h1, h2, h3]
  have h7 : 2 * sin (5 * α / 2) ^ 2 = 1 - cos (5 * α) := by
    have h8 : 2 * sin (5 * α / 2) ^ 2 = 1 - cos (5 * α) := by
      have h9 : sin (5 * α / 2) ^ 2 = (1 - cos (5 * α)) / 2 := by
        have h10 : sin (5 * α / 2) ^ 2 = (1 - cos (2 * (5 * α / 2))) / 2 := by
          rw [sin_sq_eq_half_sub]
          all_goals ring
        have h11 : 2 * (5 * α / 2) = 5 * α := by ring
        rw [h11] at h10
        linarith [h10]
      linarith [h9]
    linarith [h8]
  have h8 : cos (5 * α) = cos (3 * α) * cos (2 * α) - sin (3 * α) * sin (2 * α) := by
    have h9 : cos (5 * α) = cos (3 * α + 2 * α) := by ring_nf
    rw [h9]
    rw [cos_add]
  have h9 : sin (2 * α) = 2 * sin α * cos α := by
    rw [sin_two_mul]
  have h10 : cos (2 * α) = 1 - 2 * sin α ^ 2 := by
    have h9 : cos (2 * α) = 1 - 2 * sin α ^ 2 := by
      rw [cos_two_mul, sin_sq]
      ring_nf
    linarith
  have h11 : sin (3 * α) = 3 * sin α - 4 * sin α ^ 3 := by
    rw [sin_three_mul]
  rw [h7]
  rw [h8, h9, h10, h11]
  have h21 : cos (3 * α) = 4 * cos α ^ 3 - 3 * cos α := by
    rw [cos_three_mul]
  rw [h21]
  have h24 : sin α ^ 2 = 1 - cos α ^ 2 := by
    have h15 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    linarith
  rw [h24]
  nlinarith [sq_nonneg (sin α ^ 2 - cos α ^ 2), sq_nonneg (sin α - cos α), sq_nonneg (sin α + cos α), Real.sin_sq_add_cos_sq α, sq_nonneg (sin α ^ 2 - (1 : ℝ) / 2), sq_nonneg (cos α ^ 2 - (1 : ℝ) / 2)]