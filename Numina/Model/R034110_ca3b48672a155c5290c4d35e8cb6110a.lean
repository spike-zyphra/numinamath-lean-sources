import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_13549 (r : ℝ) (θ : ℝ) (z : ℝ)
  (h₀ : r = 5) (h₁ : θ = 3 * π / 2) (h₂ : z = 4) :
  r * cos θ = 0 ∧ r * sin θ = -5 ∧ z = 4 := by
  have hx : r * cos θ = 0 := by
    rw [h₀, h₁]
    have h3 : cos (3 * π / 2) = 0 := by
      have h4 : 3 * π / 2 = π + (π / 2) := by
        ring_nf
      rw [h4]
      have h5 : cos (π + (π / 2)) = - cos (π / 2) := by
        rw [cos_add]
        simp [cos_pi, sin_pi]
        <;> ring_nf <;> simp [cos_pi, sin_pi]
      rw [h5]
      simp [cos_pi_div_two]
    norm_num [h3]
    all_goals linarith
  have hy : r * sin θ = -5 := by
    rw [h₀, h₁]
    have h3 : sin (3 * π / 2) = -1 := by
      have h4 : 3 * π / 2 = π + (π / 2) := by
        ring_nf
      rw [h4]
      have h5 : sin (π + (π / 2)) = - sin (π / 2) := by
        rw [sin_add]
        simp [cos_pi, sin_pi]
        <;> ring_nf <;> simp [cos_pi, sin_pi]
      rw [h5]
      norm_num [sin_pi_div_two]
    norm_num [h3]
    all_goals linarith
  constructor
  · exact hx
  constructor
  · exact hy
  · exact h₂