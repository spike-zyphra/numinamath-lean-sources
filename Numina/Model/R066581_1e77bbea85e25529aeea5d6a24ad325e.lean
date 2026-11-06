import Mathlib

theorem inequalities_63985 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a + b)^3 / 4 ≥ a^2 * b + a * b^2 := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2 * b),
            sq_nonneg (a + b - 2 * a), sq_nonneg (a * b), sq_nonneg (a - b),
            mul_pos ha hb
          ]