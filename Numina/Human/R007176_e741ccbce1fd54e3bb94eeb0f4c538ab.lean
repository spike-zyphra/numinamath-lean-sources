import Mathlib

/- I have the following terms of an arithmetic sequence: $\frac{1}{2}, x-1, 3x, \ldots$. Solve for $x$. -/
theorem algebra_10252 (x : ℝ) (h : ∃ d, x - 1 = 1 / 2 + d ∧ 3 * x = x - 1 + d) :
    x = -5 / 2 := by 
  obtain ⟨d, h₀, h₁⟩ := h
  linarith