import Mathlib

/- Rewrite the expression $g^4 + 12g^2 + 9$ in the form $c(g^2 + p)^2 + q$. What is $q$? -/
theorem algebra_20389 {c p q : ℝ} (h : ∀ g : ℝ, c * (g ^ 2 + p) ^ 2 + q = g ^ 4 + 12 * g ^ 2 + 9) :
    q = -27 := by
  nlinarith [h 0, h 1, h (-1), h 2, h (-2), h 3, h (-3)]