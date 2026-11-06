import Mathlib

open Real

theorem inequalities_269072 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a * b = 1 ∧ c * d = 1) (h2 : a * c = 1 ∧ b * d = 1) :
    a * (b + 1) + b * (c + 1) + c * (d + 1) + d * (a + 1) ≥
    1 / 2 * (a + 1) * (b + 1) * (c + 1) * (d + 1) := by 
  rcases h1 with ⟨hab, hcd⟩
  rcases h2 with ⟨hac, hbd⟩
  nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, 
          sq_nonneg (a * b - 1), sq_nonneg (c * d - 1), 
          sq_nonneg (a * c - 1), sq_nonneg (b * d - 1), 
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (d - 1)]