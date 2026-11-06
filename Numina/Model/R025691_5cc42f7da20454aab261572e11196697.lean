import Mathlib

theorem inequalities_602355 (a b c : ℝ) :
    3 * (b^2 - b * c + c^2) * (c^2 - c * a + a^2) * (a^2 - a * b + b^2) ≥
    b^3 * c^3 + c^3 * a^3 + a^3 * b^3 := by 
  nlinarith [
    sq_nonneg (a * b - b * c), 
    sq_nonneg (b * c - c * a), 
    sq_nonneg (c * a - a * b), 
    sq_nonneg (a - b), 
    sq_nonneg (b - c), 
    sq_nonneg (c - a), 
    sq_nonneg (a * (a - b)), 
    sq_nonneg (a * (a - c)), 
    sq_nonneg (b * (b - c)), 
    sq_nonneg (b * (b - a)), 
    sq_nonneg (c * (c - a)), 
    sq_nonneg (c * (c - b)), 
    sq_nonneg (a * b - c^2), 
    sq_nonneg (b * c - a^2), 
    sq_nonneg (c * a - b^2)
  ]