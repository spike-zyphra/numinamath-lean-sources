import Mathlib

theorem algebra_319990 {a b c : ℝ} (ha : 0 < a) (hc : 0 < c) (hb : 0 < b)
    (hord : a > b ∧ b > c) (hroots : ∃ x : ℝ, x^2 - (a + b + c) * x + (a * b + b * c + c * a) = 0) :
    ¬(a < b + c ∧ b < a + c ∧ c < a + b) := by
  -- Assume that a, b, c are sides of a triangle for contradiction
  intro h
  rcases h with ⟨hc1, hc2, hc3⟩
  rcases hroots with ⟨x, hx⟩
  have h1 : (a + b + c) ^ 2 ≥ 4 * (a * b + b * c + c * a) := by
    nlinarith [sq_nonneg (x - (a + b + c) / 2), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h6 : (a + b + c) ^ 2 < 4 * (a * b + b * c + c * a) := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
              sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
              hc1, sq_nonneg (a - (b + c)), mul_pos ha (show 0 < b + c by linarith)]
  -- Contradiction
  nlinarith