import Mathlib

theorem inequalities_46560 {a b : ℝ} (h : a^3 + b^3 - 6*a*b = -11) :
    -7/3 < a + b ∧ a + b < -2 := by
  constructor
  · -- We need to prove -7/3 < a + b
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b + 2), sq_nonneg (a - 2), sq_nonneg (b - 2),
        sq_nonneg (a + b + 4), sq_nonneg (a + b - 1), sq_nonneg (a - b), sq_nonneg (a + b + 2),
        sq_nonneg (a - b), sq_nonneg (a + b - 2), sq_nonneg ((a + b)^2 - 4),
        sq_nonneg (a^2 - b^2), sq_nonneg (a + 2), sq_nonneg (b + 2),
        sq_nonneg (a - b), sq_nonneg (a + b + 2), sq_nonneg (a - b), sq_nonneg (a + 2), sq_nonneg (b + 2)]
  · -- We need to prove a + b < -2
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b + 2), sq_nonneg (a - 2), sq_nonneg (b - 2),
        sq_nonneg (a + b + 4), sq_nonneg (a + b - 1), sq_nonneg (a - b), sq_nonneg (a + b + 2),
        sq_nonneg (a - b), sq_nonneg (a + b - 2), sq_nonneg ((a + b)^2 - 4),
        sq_nonneg (a^2 - b^2), sq_nonneg (a + 2), sq_nonneg (b + 2),
        sq_nonneg (a - b), sq_nonneg (a + b + 2), sq_nonneg (a - b), sq_nonneg (a + 2), sq_nonneg (b + 2)]