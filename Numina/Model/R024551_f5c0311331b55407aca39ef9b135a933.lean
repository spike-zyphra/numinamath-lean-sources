import Mathlib

/- Given the quadratic function $y=a{{x}^{2}}+bx+c\geqslant 0(a<{}b)$, then the minimum value of $M=\frac{a+2b+4c}{b-a}$ is ___          ___. -/
theorem algebra_11691 (a b c : ℝ) (ha : a < b) (h : ∀ x, a * x ^ 2 + b * x + c ≥ 0) :
    (a + 2 * b + 4 * c) / (b - a) ≥ 8 := by
  have h1 := h (-2)
  have h2 := h (-1.5)
  have h3 := h (-1)
  have h4 := h (-0.5)
  have h5 := h 0
  have h6 := h 0.5
  have h7 := h 1
  have h8 := h 1.5
  have h9 := h 2
  have hb1 : b - a > 0 := by linarith
  have h10 : a + 2 * b + 4 * c ≥ 8 * (b - a) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - 2 * a), sq_nonneg (c - a), sq_nonneg (c - b), 
      sq_nonneg (a - 0.5 * b), sq_nonneg (b - 1.5 * a), 
      h1, h2, h3, h4, h5, h6, h7, h8, h9
      ]
  have h11 : (a + 2 * b + 4 * c) / (b - a) ≥ 8 := by
    apply (le_div_iff₀ (by linarith)).mpr
    linarith [h10]
  exact h11