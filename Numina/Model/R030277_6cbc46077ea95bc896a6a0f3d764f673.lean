import Mathlib

theorem algebra_19401 {k : ℝ → ℝ} (f : ℝ → ℝ)
    (h₀ : ∀ x, x > 3 → f x = k x)
    (h₁ : ∀ x, x ≤ 3 → f x = x ^ 2 - 6 * x + 12)
    (h₂ : ∀ x, f (f x) = x) :
    ∀ x > 3, k x = -Real.sqrt (x - 3) + 3 := by
  intro x hx
  have h3 : f (3 - Real.sqrt (x - 3)) = x := by
    have h4 : (3 - Real.sqrt (x - 3) : ℝ) ≤ 3 := by
      have h5 : Real.sqrt (x - 3) ≥ 0 := Real.sqrt_nonneg (x - 3)
      linarith
    have h6 : f (3 - Real.sqrt (x - 3)) = (3 - Real.sqrt (x - 3)) ^ 2 - 6 * (3 - Real.sqrt (x - 3)) + 12 := h₁ (3 - Real.sqrt (x - 3)) h4
    rw [h6]
    have h7 : (Real.sqrt (x - 3)) ^ 2 = x - 3 := Real.sq_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg (x - 3), Real.sq_sqrt (show (0 : ℝ) ≤ x - 3 by linarith)]
  have h4 : f (f (3 - Real.sqrt (x - 3))) = 3 - Real.sqrt (x - 3) := h₂ (3 - Real.sqrt (x - 3))
  have h8 : f (f (3 - Real.sqrt (x - 3))) = f x := by
    rw [h3]
  have h9 : f x = 3 - Real.sqrt (x - 3) := by 
    linarith [h4, h8]
  have h10 : f x = k x := by 
    apply h₀ x
    exact hx
  have h11 : k x = 3 - Real.sqrt (x - 3) := by 
    linarith [h9, h10]
  linarith [h11]