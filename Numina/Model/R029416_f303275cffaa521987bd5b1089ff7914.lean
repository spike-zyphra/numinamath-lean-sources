import Mathlib

open Real Set
open scoped Real

theorem algebra_162882 (x : ℝ) :
  sin (2 * x - π) * cos (x - 3 * π) + sin (2 * x - 9 * π / 2) * cos (x + π / 2) =
  sin (3 * x) := by
  have h1 : sin (2 * x - π) = - sin (2 * x) := by
    have h2 : 2 * x - π = 2 * x - π := by rfl
    rw [show 2 * x - π = (2 * x) - π by ring]
    rw [sin_sub, sin_pi, cos_pi]
    ring
  have h2 : cos (x - 3 * π) = - cos x := by
    have h3 : cos (x - 3 * π) = cos (x - π - 2 * π) := by ring_nf
    rw [h3]
    have h4 : cos (x - π - 2 * π) = cos (x - π) := by
      rw [show x - π - 2 * π = (x - π) - 2 * π by ring]
      rw [cos_sub_two_pi]
    rw [h4]
    have h5 : cos (x - π) = -cos x := by
      rw [cos_sub, cos_pi, sin_pi]
      ring
    rw [h5]
  have h3 : sin (2 * x - π) * cos (x - 3 * π) = sin (2 * x) * cos x := by
    rw [h1, h2]
    ring
  have h4 : sin (2 * x - 9 * π / 2) = -cos (2 * x) := by 
    have h5 : 2 * x - 9 * π / 2 = (2 * x - π / 2) - 4 * π := by 
      linarith [pi_pos]
    rw [h5]
    have h6 : sin ((2 * x - π / 2) - 4 * π) = sin (2 * x - π / 2) := by 
      have h7 : sin ((2 * x - π / 2) - 4 * π) = sin ((2 * x - π / 2) - 2 * π - 2 * π) := by ring_nf
      rw [h7]
      rw [show sin ((2 * x - π / 2) - 2 * π - 2 * π) = sin ((2 * x - π / 2) - 2 * π) by rw [sin_sub_two_pi]]
      rw [show sin ((2 * x - π / 2) - 2 * π) = sin (2 * x - π / 2) by rw [sin_sub_two_pi]]
    rw [h6]
    have h7 : sin (2 * x - π / 2) = -cos (2 * x) := by 
      rw [sin_sub, sin_pi_div_two, cos_pi_div_two]
      ring
    rw [h7]
  have h5 : cos (x + π / 2) = -sin x := by 
    rw [cos_add, cos_pi_div_two, sin_pi_div_two]
    ring
  have h6 : sin (2 * x - 9 * π / 2) * cos (x + π / 2) = cos (2 * x) * sin x := by 
    rw [h4, h5]
    ring
  calc 
    sin (2 * x - π) * cos (x - 3 * π) + sin (2 * x - 9 * π / 2) * cos (x + π / 2)
        = sin (2 * x) * cos x + cos (2 * x) * sin x := by 
          rw [h3, h6]
    _ = sin (3 * x) := by 
      rw [show 3 * x = 2 * x + x by ring]
      rw [show sin (2 * x + x) = sin (2 * x) * cos x + cos (2 * x) * sin x by 
        rw [sin_add]
      ]
      <;> ring