import Mathlib

theorem inequalities_602653 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 3) :
    1 ≤ 1 / (1 + 2 * a * b) + 1 / (1 + 2 * b * c) + 1 / (1 + 2 * c * a) := by
  have h1 : 0 < (1 + 2 * a * b) * (1 + 2 * b * c) * (1 + 2 * c * a) := by
    positivity 
  suffices (1 / (1 + 2 * a * b) + 1 / (1 + 2 * b * c) + 1 / (1 + 2 * c * a) - 1) ≥ 0 by linarith
  have h2 : (1 / (1 + 2 * a * b) + 1 / (1 + 2 * b * c) + 1 / (1 + 2 * c * a) - 1) = ( (1 + 2 * b * c) * (1 + 2 * c * a) + (1 + 2 * a * b) * (1 + 2 * c * a) + (1 + 2 * a * b) * (1 + 2 * b * c) - (1 + 2 * a * b) * (1 + 2 * b * c) * (1 + 2 * c * a) ) / ( (1 + 2 * a * b) * (1 + 2 * b * c) * (1 + 2 * c * a) ) := by
    field_simp
    ring
  rw [h2]
  apply div_nonneg
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
    sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (b * c - c * a), 
    sq_nonneg (a * c - b * a), sq_nonneg (b * a - c * b), sq_nonneg (c * a - b * c), 
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc ]
  all_goals 
    positivity