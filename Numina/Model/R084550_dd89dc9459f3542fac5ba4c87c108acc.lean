import Mathlib

open Real
open scoped BigOperators

theorem algebra_150699 (p q : ℝ × ℝ)
  (hp : ‖p‖ = 4) (hq : ‖q‖ = 3)
  (h : p.1 * q.2 - p.2 * q.1 = -4 * 3 * sin (3 * π / 4)) :
  (3 * p.1 + 2 * q.1) * (2 * p.2 - q.2) - (3 * p.2 + 2 * q.2) * (2 * p.1 - q.1) = 42 * sqrt 2 := by 
  have h1 : (3 * p.1 + 2 * q.1) * (2 * p.2 - q.2) - (3 * p.2 + 2 * q.2) * (2 * p.1 - q.1) = -7 * (p.1 * q.2 - p.2 * q.1) := by
    ring_nf
  rw [h1]
  rw [h]
  have h2 : sin (3 * π / 4) = Real.sqrt 2 / 2 := by 
    have h1 : sin (3 * π / 4) = sin (π - (π / 4)) := by 
      ring_nf
    rw [h1]
    rw [sin_pi_sub]
    have h3 : sin (π / 4) = Real.sqrt 2 / 2 := by 
      exact sin_pi_div_four
    rw [h3]
  rw [h2]
  ring_nf
  <;> simp [Real.sqrt_sq]
  <;> ring_nf