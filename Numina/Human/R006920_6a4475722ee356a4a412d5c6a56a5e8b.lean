import Mathlib

/- Let $P(x) = 4x^3 - 2x^2 + 7x - 1$, and let $Q(x) = P(x)^2$. What is the y-intercept of $Q(x)$? -/
theorem algebra_20095 {P Q : ℝ → ℝ} (hP : P = fun x => 4 * x ^ 3 - 2 * x ^ 2 + 7 * x - 1)
    (hQ : Q = fun x => (P x) ^ 2) :
    Q 0 = 1 := by 
  rw [hQ, hP]; simp