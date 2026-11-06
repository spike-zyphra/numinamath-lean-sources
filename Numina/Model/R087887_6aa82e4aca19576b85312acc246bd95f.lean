import Mathlib

theorem inequalities_277037 (a b c : ℝ) :
    (a + b - c) ^ 2 + (a + c - b) ^ 2 + (b + c - a) ^ 2 ≥ a * b + b * c + a * c := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)]