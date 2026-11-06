import Mathlib

/- Sviatoslav solved the quadratic equation $x^2-x-1=0$ by completing the square. In the process, he came up with the equivalent equation $$(x+a)^2 = b,$$where $a$ and $b$ are constants.

What is $b$? -/
theorem algebra_19914 {a b : ℝ} (h : ∀ x, x^2 - x - 1 = (x + a)^2 - b) :
    b = 5 / 4 := by
  have h₁ := h 0
  have h₂ := h 1
  have h₃ := h 2
  simp at h₁ h₂ h₃
  nlinarith