import Mathlib

/- Consider the following function $g(x)$ defined as\[(x^{2^{2008}-1}-1)g(x) = (x+1)(x^2+1)(x^4+1)\cdots (x^{2^{2007}}+1) - 1\]Find $g(2)$.
 -/
theorem algebra_13189 {g : ℝ → ℝ}
    (h : ∀ x, (x^(2^2008 - 1) - 1) * g x = ∏ i ∈ Finset.range 2008, (x^(2^i) + 1) - 1) :
    g 2 = 2 := by
  have h1 := h 2
  have h2 := h 1
  have h3 := h 0
  simp at h1 h2 h3
  linarith