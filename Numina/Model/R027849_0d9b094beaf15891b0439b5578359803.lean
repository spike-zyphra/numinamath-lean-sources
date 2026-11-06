import Mathlib

open Real Set
open scoped Real

theorem inequalities_132401 (x : ℝ) (h : sin x < cos (x / 2)) (h' : cos (x / 2) < 0) :
    cos x < 1 / 2 := by 
  have h3 : cos x = 2 * (cos (x / 2)) ^ 2 - 1 := by 
    have h4 : cos x = cos (2 * (x / 2)) := by ring_nf
    rw [h4]
    rw [cos_two_mul]
  have h4 : sin x = 2 * sin (x / 2) * cos (x / 2) := by 
    have h5 : sin x = sin (2 * (x / 2)) := by ring_nf
    rw [h5]
    rw [sin_two_mul]
  have h6 : 2 * sin (x / 2) * cos (x / 2) < cos (x / 2) := by 
    linarith [h, h4]
  have h7 : sin (x / 2) > 1 / 2 := by 
    nlinarith [h6, h']
  have h8 : (cos (x / 2)) ^ 2 < 3 / 4 := by 
    nlinarith [Real.sin_sq_add_cos_sq (x / 2), sq_nonneg (sin (x / 2) - 1 / 2), h7, sq_nonneg (cos (x/2))]
  nlinarith [h3, h8]