import Mathlib

open Real Set
open scoped Real

theorem inequalities_325267 (a b : ℝ) (h : ∀ x : ℝ, a * cos x + b * cos (2 * x) ≥ -1) :
    a + b ≤ 2 := by
  have h1 := h (2 * Real.pi / 3)
  have h2 : cos (2 * Real.pi / 3) = -1 / 2 := by
    have h1 : cos (2 * Real.pi / 3) = cos (Real.pi - Real.pi / 3) := by 
      ring_nf
    rw [h1]
    rw [cos_pi_sub]
    have h3 : cos (Real.pi / 3) = 1 / 2 := cos_pi_div_three
    linarith
  have h3 : cos (2 * (2 * Real.pi / 3)) = -1 / 2 := by
    have h4 : 2 * (2 * Real.pi / 3) = Real.pi + Real.pi / 3 := by 
      ring_nf
    rw [h4]
    have h5 : cos (Real.pi + Real.pi / 3) = -cos (Real.pi / 3) := by 
      rw [cos_add]
      rw [cos_pi, sin_pi]
      all_goals ring_nf <;> norm_num
      <;> linarith [cos_pi_div_three]
    rw [h5]
    have h4 : cos (Real.pi / 3) = 1 / 2 := cos_pi_div_three
    linarith
  rw [show 2 * (2 * Real.pi / 3) = 2 * (2 * Real.pi / 3) by rfl] at h1
  rw [h2, h3] at h1
  nlinarith