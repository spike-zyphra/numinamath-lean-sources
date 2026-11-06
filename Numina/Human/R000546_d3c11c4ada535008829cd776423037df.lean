import Mathlib

/- If we express $x^2 - 5x$ in the form $a(x - h)^2 + k$, then what is $k$? -/
theorem algebra_12269 (a h k : ℝ) (ha : a ≠ 0) (h1 : ∀ x, x^2 - 5 * x = a * (x - h)^2 + k) :
    k = -25 / 4 := by
  have h2 := h1 0
  have h3 := h1 5
  have h4 := h1 2
  simp at h2 h3 h4
  nlinarith