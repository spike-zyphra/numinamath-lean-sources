import Mathlib

theorem algebra_195685 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hroots : ∃ x : ℝ, x^2 + a * x + 2 * b = 0 ∧ ∃ x : ℝ, x^2 + 2 * b * x + a = 0) :
    a + b ≥ 6 := by
  rcases hroots with ⟨x1, h1, ⟨x2, h2⟩⟩
  have h11 : a ^ 2 - 8 * b ≥ 0 := by
    nlinarith [sq_nonneg (x1 + a / 2)]
  have h22 : b ^ 2 - a ≥ 0 := by
    nlinarith [sq_nonneg (x2 + b)]
  nlinarith [sq_nonneg (a - 4), sq_nonneg (b - 2), 
    sq_nonneg (a ^ 2 - 8 * b), sq_nonneg (b ^ 2 - a),
    mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith),
    sq_nonneg (a - 4 * b), sq_nonneg (b - 2)]