import Mathlib

theorem algebra_16351 (x y : ℝ) (h : x^2 + y^2 = 14 * x + 6 * y + 6) :
    3 * x + 4 * y ≤ 73 ∧ (∃ a b : ℝ, a ^ 2 + b ^ 2 = 14 * a + 6 * b + 6 ∧ 3 * a + 4 * b = 73) := by
  have h_max : 3 * x + 4 * y ≤ 73 := by
    linarith [sq_nonneg (x - 59 / 5), sq_nonneg (y - 47 / 5), h]
  have h_achieved : ∃ a b : ℝ, a ^ 2 + b ^ 2 = 14 * a + 6 * b + 6 ∧ 3 * a + 4 * b = 73 := by
    use 59 / 5, 47 / 5
    constructor
    <;> norm_num
  exact ⟨h_max, h_achieved⟩