import Mathlib

theorem inequalities_205399 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hle : a ≤ b ∧ b ≤ c ∧ c ≤ d) (hsum : 1 ≤ a + b + c + d) :
    a^2 + 3 * b^2 + 5 * c^2 + 7 * d^2 ≥ 1 := by 
  rcases hle with ⟨hab, hbc, hcd⟩
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d),
            sq_nonneg (a - 1/4), sq_nonneg (b - 1/4), sq_nonneg (c - 1/4), sq_nonneg (d - 1/4),
            mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]