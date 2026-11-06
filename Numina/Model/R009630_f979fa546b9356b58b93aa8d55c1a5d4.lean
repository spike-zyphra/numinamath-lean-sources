import Mathlib

theorem algebra_9169 {f : ℝ → ℝ} (hfodd : ∀ x, f (- x) = -f x) (hf : ∀ x ≤ 0, f x = x ^ 2 - 2 * x) :
    ∀ x > 0, f x = -x ^ 2 - 2 * x := by 
  intro x hx
  have h₁ : -x ≤ 0 := by linarith
  have h_eq1 : f (-x) = (-x)^2 - 2 * (-x) := hf (-x) h₁ 
  have h_eq2 : f (-x) = -f x := hfodd x 
  have h_eq3 : -f x = (-x)^2 - 2 * (-x) := by 
    linarith 
  nlinarith