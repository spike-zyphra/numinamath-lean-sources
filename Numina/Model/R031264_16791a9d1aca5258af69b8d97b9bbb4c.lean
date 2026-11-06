import Mathlib
theorem algebra_606026 : (∀ a b c : ℝ, a ^ 2 + b ^ 2 + c ^ 2 = 1 → a * b + b * c + c * a - 2 * (a + b + c) ≥ -5 / 2) ∧ ¬(∃ a b c : ℝ, a ^ 2 + b ^ 2 + c ^ 2 = 1 ∧ a * b + b * c + c * a - 2 * (a + b + c) = -5 / 2) := by
  constructor
  · -- First part: proving the inequality for all a, b, c with a^2+b^2+c^2=1
    intro a b c h1
    nlinarith [sq_nonneg (a + b + c - 2), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b + c), h1]
  · -- Second part: proving the non-existence of the equality case
    intro h
    rcases h with ⟨a, b, c, h1, h2⟩
    have h3 : (a + b + c) ^ 2 = 4 := by
      nlinarith [h1, sq_nonneg (a + b + c - 2)]
    have h4 : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    have h5 : 3 * (a ^ 2 + b ^ 2 + c ^ 2) = 3 := by
      linarith [h1]
    nlinarith [h1, h2, h3, h4, h5]