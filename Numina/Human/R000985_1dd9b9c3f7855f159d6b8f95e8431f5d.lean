import Mathlib

/- Find the constant $c$ such that $$(x^2-4x+3)(x+5) - (x^2+4x-5)(x-c)=0$$ for all $x.$ -/
theorem algebra_19585 {c : ℝ} (h : ∀ x, (x ^ 2 - 4 * x + 3) * (x + 5) - (x ^ 2 + 4 * x - 5) * (x - c) = 0) :
    c = 3 := by 
  have h₁ := h (-5)
  have h₂ := h 0
  have h₃ := h 1
  linarith