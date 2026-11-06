import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_181291 {f : ℝ → ℝ} (hf : f = λ x => sin (4 * x) * cos (4 * x)) :
    deriv f (π / 3) = -2 := by
  rw [hf]
  have h1 : deriv (fun (x : ℝ) => sin (4 * x) * cos (4 * x)) (π / 3) =
      4 * cos (4 * (π / 3)) * cos (4 * (π / 3)) + sin (4 * (π / 3)) * (-4 * sin (4 * (π / 3))) := by 
    simp [deriv_mul, deriv_pow, deriv_id'', mul_comm]
    all_goals field_simp [differentiableAt_id', differentiableAt_sin, differentiableAt_cos]
    <;> ring
  rw [h1]
  have h2 : cos (4 * (π / 3)) = -1 / 2 := by
    have h3 : 4 * (π / 3) = π / 3 + π := by ring
    rw [h3]
    have h4 : cos (π / 3 + π) = -cos (π / 3) := by 
      rw [cos_add_pi]
    rw [h4]
    rw [cos_pi_div_three]
    all_goals linarith
  have h3 : sin (4 * (π / 3)) = -Real.sqrt 3 / 2 := by
    have h3' : 4 * (π / 3) = π / 3 + π := by ring
    rw [h3']
    have h4 : sin (π / 3 + π) = -sin (π / 3) := by 
      rw [sin_add_pi]
    rw [h4]
    rw [sin_pi_div_three]
    all_goals ring
  rw [h2, h3]
  ring_nf
  <;> norm_num