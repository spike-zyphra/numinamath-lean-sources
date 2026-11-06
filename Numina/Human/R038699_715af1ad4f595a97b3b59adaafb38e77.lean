import Mathlib

/- Let $0\le a\le b\le c$ be real numbers. Prove that
$$
(a+3b)(b+4c)(c+2a)\ge 60abc
$$
 -/
theorem inequalities_87153 (a b c : ℝ) (h₀ : 0 ≤ a) (h₁ : a ≤ b) (h₂ : b ≤ c) :
    (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (c + a)]