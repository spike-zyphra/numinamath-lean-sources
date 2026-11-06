import Mathlib

theorem algebra_200785 {a b c d : ℝ} (ha : a ≠ 0) (h1 : 0 < 2 * (a * 2^3 + b * 2^2 + c * 2 + d))
    (h2 : 2 * (a * 2^3 + b * 2^2 + c * 2 + d) = 3 * (a * 3^3 + b * 3^2 + c * 3 + d))
    (h3 : 3 * (a * 3^3 + b * 3^2 + c * 3 + d) = 4 * (a * 4^3 + b * 4^2 + c * 4 + d))
    (h4 : 4 * (a * 4^3 + b * 4^2 + c * 4 + d) < 1) :
    0 < a * 1^3 + b * 1^2 + c * 1 + d + a * 5^3 + b * 5^2 + c * 5 + d ∧
    a * 1^3 + b * 1^2 + c * 1 + d + a * 5^3 + b * 5^2 + c * 5 + d < 1 := by
  constructor
  · -- Proof that $0 < a * 1^3 + b * 1^2 + c * 1 + d + a * 5^3 + b * 5^2 + c * 5 + d$
    nlinarith
  · -- Proof that $a * 1^3 + b * 1^2 + c * 1 + d + a * 5^3 + b * 5^2 + c * 5 + d < 1$
    nlinarith