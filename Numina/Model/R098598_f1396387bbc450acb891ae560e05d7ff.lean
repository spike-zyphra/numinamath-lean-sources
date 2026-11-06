import Mathlib

theorem algebra_176365 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : x * (1 + x + x ^ 2 + x ^ 3 + x ^ 4) = 2 * (x ^ 4 + x ^ 5 + x ^ 6 + x ^ 7))
    (h2 : x * (1 + x) = 48) :
    x * (1 + x + x ^ 2 + x ^ 3 + x ^ 4) = 62 := by
        nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x^2 - x - 6), sq_nonneg (x - 3), sq_nonneg (x - 4),
                  sq_nonneg (x^2 - 16), sq_nonneg (x^2 - 24), sq_nonneg (x^2 - 16 * x), sq_nonneg (x - 8)]