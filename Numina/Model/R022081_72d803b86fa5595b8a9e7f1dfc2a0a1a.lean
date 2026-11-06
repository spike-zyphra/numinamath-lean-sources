import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_23089 (r : ℝ → ℝ) (hr : r = λ θ => cos θ + sin θ) :
    ∀ θ, r θ = √2 * sin (θ + π / 4) := by 
  intro θ
  rw [hr]
  have h1 : cos θ + sin θ = Real.sqrt 2 * sin (θ + Real.pi / 4) := by 
    have h2 : sin (θ + Real.pi / 4) = sin θ * cos (Real.pi / 4) + cos θ * sin (Real.pi / 4) := by 
      rw [sin_add]
    rw [h2]
    have h3 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by 
      exact cos_pi_div_four
    have h4 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by 
      exact sin_pi_div_four
    rw [h3, h4]
    ring_nf
    <;> simp [Real.sqrt_sq]
    <;> ring
  simpa using h1