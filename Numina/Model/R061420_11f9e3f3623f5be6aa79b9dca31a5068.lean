import Mathlib

theorem inequalities_317498 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) * (a^4 + b^4) ≥ (a^2 + b^2) * (a^3 + b^3) := by
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a - b), sq_nonneg (a + b), 
          sq_nonneg (a * b), sq_nonneg (a^2 - a * b), sq_nonneg (a * b - b^2)]