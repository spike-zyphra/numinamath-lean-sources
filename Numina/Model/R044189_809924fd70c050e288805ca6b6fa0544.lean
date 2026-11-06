import Mathlib

open Real Set
open scoped Real

theorem algebra_86623 (α β γ : ℝ) (h : α + β + γ = π) :
    sin (2*α) + sin (2*β) + sin (2*γ) =
    2 * (sin α + sin β + sin γ) * (cos α + cos β + cos γ) -
    2 * (sin α + sin β + sin γ) := by
  have h1 : γ = π - (α + β) := by
    linarith
  have h2 : sin (2 * γ) = - sin (2 * (α + β)) := by 
    have h3 : 2 * γ = 2 * (π - (α + β)) := by
      rw [show γ = π - (α + β) by linarith]
      <;> ring
    rw [h3]
    have h4 : 2 * (π - (α + β)) = 2 * π - 2 * (α + β) := by ring
    rw [h4]
    have h5 : sin (2 * π - 2 * (α + β)) = - sin (2 * (α + β)) := by 
      rw [show 2 * π - 2 * (α + β) = 2 * π - (2 * (α + β)) by ring]
      rw [sin_sub, sin_two_pi, cos_two_pi]
      simp
    exact h5
  have h3 : sin (2 * (α + β)) = sin (2 * α) * cos (2 * β) + cos (2 * α) * sin (2 * β) := by 
    rw [show 2 * (α + β) = 2 * α + 2 * β by ring]
    rw [sin_add]
    <;> ring_nf
  have h3a : sin (2 * α) = 2 * sin α * cos α := by 
    rw [sin_two_mul]
  have h3b : sin (2 * β) = 2 * sin β * cos β := by 
    rw [sin_two_mul]
  have h3c : cos (2 * α) = 2 * cos α ^ 2 - 1 := by 
    rw [cos_two_mul]
  have h3d : cos (2 * β) = 2 * cos β ^ 2 - 1 := by 
    rw [cos_two_mul]
  have h4a : sin γ = sin α * cos β + cos α * sin β := by 
    have h4 : γ = π - (α + β) := by 
      linarith
    rw [h4]
    have h5 : sin (π - (α + β)) = sin (α + β) := by 
      rw [sin_pi_sub]
    have h6 : sin (α + β) = sin α * cos β + cos α * sin β := by 
      rw [sin_add]
    rw [h5, h6]
  have h4b : cos γ = sin α * sin β - cos α * cos β := by
    have h4 : γ = π - (α + β) := by 
      linarith
    rw [h4]
    have h5 : cos (π - (α + β)) = -cos (α + β) := by 
      rw [cos_pi_sub]
    have h6 : cos (α + β) = cos α * cos β - sin α * sin β := by 
      rw [cos_add]
    rw [h5, h6]
    all_goals ring
  rw [h2, h3]
  rw [h3a, h3b, h3c, h3d] at *
  simp [h4a, h4b] at *
  <;> ring_nf
  <;> simp [sin_sq, cos_sq]
  <;> ring