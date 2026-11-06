import Mathlib

theorem algebra_125946 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) * f (x - y) = (f x + f y)^2 - 4 * x^2 * f y) :
    ∀ x, f x = 0 ∨ f x = x^2 := by
  have h1 : f 0 = 0 := by
    have h00 := h 0 0
    norm_num at h00
    nlinarith
  have eq1 : ∀ x : ℝ, f x = 0 ∨ f x = x ^ 2 := by
    intro x
    have h2x := h x x
    have eq2 := h2x
    simp [show f 0 = 0 by linarith [h1]] at eq2
    have h2 : f x * (f x - x ^ 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- f x = 0 
      left
      linarith 
    · -- f x - x^2 = 0 
      right
      linarith 
  intro x
  specialize eq1 x
  simpa using eq1