import Mathlib

open Real Set
open scoped Real

theorem algebra_9373 {φ : ℝ} (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = sin (x + 2 * φ) - 2 * sin φ * cos (x + φ)) :
  f (π / 4) = sqrt 2 / 2 := by
  have h1 : ∀ x, f x = sin x := by
    intro x
    rw [h₀ x]
    have h2 : sin (x + 2 * φ) = sin (x + φ + φ) := by ring_nf
    rw [h2]
    have h3 : sin (x + φ + φ) = sin (x + φ) * cos φ + cos (x + φ) * sin φ := by 
      rw [sin_add]
    rw [h3]
    have h5 : sin (x + φ) * cos φ + cos (x + φ) * sin φ - 2 * sin φ * cos (x + φ) = 
      sin x := by 
      have h6 : sin (x + φ) * cos φ + cos (x + φ) * sin φ - 2 * sin φ * cos (x + φ) =
        sin ((x + φ) - φ) := by 
        rw [sin_sub]
        ring
      rw [h6]
      have h7 : (x + φ) - φ = x := by 
          ring
      rw [h7]
    linarith [h5]
  have h2 : f (π / 4) = sin (π / 4) := h1 (π / 4)
  rw [h2]
  have h3 : sin (π / 4) = sqrt 2 / 2 := by
    exact sin_pi_div_four
  rw [h3]