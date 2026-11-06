import Mathlib

theorem algebra_930 (f : ℝ → ℝ) :
    (∀ a b : ℝ, a ≠ 0 → b ≠ 0 → f ((a ^ 2 + a * b + b ^ 2) / 3) = f (a ^ 2) + f (b ^ 2)) →
    ∀ x > 0, f x = 0 := by 
  intro h_eq
  intro x hx
  have h_eq' := h_eq (Real.sqrt x) (Real.sqrt x) (by positivity) (by positivity)
  have h2 : (Real.sqrt x ^ 2 + Real.sqrt x * Real.sqrt x + Real.sqrt x ^ 2)/3 = x := by
    have h3 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (show x ≥ 0 by linarith)
    nlinarith [Real.sqrt_nonneg x]
  have h3 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (show x ≥ 0 by linarith)
  rw [h2, h3] at h_eq'
  linarith