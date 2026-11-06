import Mathlib

theorem algebra_16351 (x y : ℝ) (h : x^2 + y^2 = 14 * x + 6 * y + 6) :
    3 * x + 4 * y ≤ 73 ∧ (∃ a b : ℝ, a ^ 2 + b ^ 2 = 14 * a + 6 * b + 6 ∧ 3 * a + 4 * b = 73) := by
  have h1 : (x - 7) ^ 2 + (y - 3) ^ 2 = 64 := by
    nlinarith
  have h2 : 3 * x + 4 * y ≤ 73 := by
    nlinarith [sq_nonneg (x - 59 / 5), sq_nonneg (y - 47 / 5),
      h1]
  constructor
  · -- Proof that 3 * x + 4 * y ≤ 73
    exact h2
  · -- Proof that there exists a, b such that a^2 + b^2 = 14 * a + 6 * b + 6 ∧ 3 * a + 4 * b = 73
    use 59 / 5, 47 / 5
    constructor
    · -- Show that a^2 + b^2 = 14 * a + 6 * b + 6
      norm_num
    · -- Show that 3 * a + 4 * b = 73
      norm_num