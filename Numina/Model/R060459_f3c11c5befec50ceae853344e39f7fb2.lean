import Mathlib
open Real Set

theorem algebra_1588 {f : ℝ → ℝ} (hf : f = λ x => sin (2 * x) * sin (4 * x)) :
    Function.Periodic f (Real.pi) := by
  rw [hf]
  intro x
  have h1 : sin (2 * (x + Real.pi)) = sin (2 * x) := by 
    have h : 2 * (x + Real.pi) = 2 * x + 2 * Real.pi := by ring
    rw [h]
    rw [sin_add_two_pi]
  have h2 : sin (4 * (x + Real.pi)) = sin (4 * x) := by
    have h : 4 * (x + Real.pi) = 4 * x + 4 * Real.pi := by ring
    rw [h]
    have h3 : sin (4 * x + 4 * Real.pi) = sin (4 * x + 2 * Real.pi + 2 * Real.pi) := by ring_nf
    rw [h3]
    have h4 : sin (4 * x + 2 * Real.pi + 2 * Real.pi) = sin (4 * x + 2 * Real.pi) := by 
      rw [show 4 * x + 2 * Real.pi + 2 * Real.pi = (4 * x + 2 * Real.pi) + 2 * Real.pi by ring]
      rw [sin_add_two_pi]
    rw [h4]
    rw [sin_add_two_pi]
  simp [h1, h2]
  all_goals ring