import Mathlib

theorem algebra_187502 {f : ℝ → ℝ} (hf : ∀ x, f (Real.sqrt x + 1) ≥ x + 2 * Real.sqrt x) :
    ∀ x, 1 ≤ x → f x ≥ x ^ 2 - 1 := by 
  intro x hx
  have h1 : f x ≥ (x - 1) ^ 2 + 2 * (x - 1) := by 
    have h2 := hf ((x - 1) ^ 2)
    have h3 : Real.sqrt ((x - 1) ^ 2) = x - 1 := by
      rw [Real.sqrt_sq (show (0 : ℝ) ≤ x - 1 by linarith)]
    rw [show Real.sqrt ((x - 1) ^ 2) + 1 = x by rw [h3]; ring] at h2
    have h4 : (x - 1) ^ 2 + 2 * Real.sqrt ((x - 1) ^ 2) = (x - 1) ^ 2 + 2 * (x - 1) := by 
      rw [h3]
    linarith [h2, h4]
  have h2 : (x - 1) ^ 2 + 2 * (x - 1) = x^2 - 1 := by ring
  linarith [h1, h2]