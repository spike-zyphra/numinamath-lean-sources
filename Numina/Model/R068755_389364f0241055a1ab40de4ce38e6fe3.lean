import Mathlib

theorem algebra_315335 (a b c d e : ℝ)
    (h₀ : a + b + c + d + e = 4) (h₁ : a^2 + b^2 + c^2 + d^2 + e^2 = 4) :
    a ≤ 8 / 5 := by
        nlinarith [sq_nonneg (b + c + d + e), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d), sq_nonneg (c - e), sq_nonneg (d - e), sq_nonneg (a - 8/5)]