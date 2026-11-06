import Mathlib

theorem inequalities_173283 (a b c : ℝ) :
    a^4 + b^4 + c^4 ≥ a * b * c * (a + b + c) := by 
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c)
     ]