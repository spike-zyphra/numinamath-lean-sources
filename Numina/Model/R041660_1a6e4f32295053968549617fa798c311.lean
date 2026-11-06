import Mathlib

theorem inequalities_69076 (a b c d : ℝ)
    (h₀ : a + b + c + d = 6)
    (h₁ : a^2 + b^2 + c^2 + d^2 = 12) :
    36 ≤ 4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) ∧
    4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) ≤ 48 := by
  constructor
  · -- Prove that 36 ≤ 4(a^3+b^3+c^3+d^3) - (a^4+b^4+c^4+d^4)
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
              sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (d - 1)]
  · -- Prove that 4(a^3+b^3+c^3+d^3) - (a^4+b^4+c^4+d^4) ≤ 48
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
              sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2), sq_nonneg (d - 2)]