import Mathlib

theorem inequalities_605765 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) :
    (a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1) * (b ^ 5 + b ^ 4 + b ^ 3 + b ^ 2 + b + 1) * (c ^ 5 + c ^ 4 + c ^ 3 + c ^ 2 + c + 1) ≥ 8 * (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1) := by

  have h₀ (x : ℝ) : x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = (x ^ 3 + 1) * (x ^ 2 + x + 1) := by ring
  rw [h₀ a, h₀ b, h₀ c]

  suffices ( (a ^ 3 + 1) * (b ^ 3 + 1) * (c ^ 3 + 1) ) ≥ 8 by
    nlinarith [this, mul_pos (mul_pos (show 0 < a ^ 2 + a + 1 by nlinarith) (show 0 < b ^ 2 + b + 1 by nlinarith)) (show 0 < c ^ 2 + c + 1 by nlinarith)]

  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1), 
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          sq_nonneg (a * b * c - 1), sq_nonneg (a^3 - 1), sq_nonneg (b^3 - 1), sq_nonneg (c^3 - 1), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc]