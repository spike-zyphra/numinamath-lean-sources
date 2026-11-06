import Mathlib

theorem algebra_282186 {a b c : ℝ} (h₀ : a^4 * b^3 * c^5 = 18) (h₁ : a^3 * b^5 * c^4 = 8) :
    a^5 * b * c^6 = 81 / 2 := by
  have h5 : a^5 * b * c^6 = (81 / 2) := by
    nlinarith [sq_nonneg (a ^ 2 - c), sq_nonneg (b ^ 2 - c), sq_nonneg (a - b), sq_nonneg (a * b - c), 
          sq_nonneg (a * c - b), sq_nonneg (b * c - a),
          sq_nonneg (a^4 * b^3 * c^5 - 18), sq_nonneg (a^3 * b^5 * c^4 - 8)]
  linarith [h5]