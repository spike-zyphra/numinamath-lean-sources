import Mathlib

theorem algebra_318010 (p q : ℝ) (h : p^3 + q^3 = 2) :
    p + q ≤ 2 ∧ ∃ p q : ℝ, p^3 + q^3 = 2 ∧ p + q = 2 := by
  have h1 : p + q ≤ 2 := by
    nlinarith [sq_nonneg (p - q), sq_nonneg (p + q - 2), sq_nonneg (p - 1), sq_nonneg (q - 1), sq_nonneg (p + q - 2)]
  constructor
  · exact h1
  · -- Show that there exist real numbers p and q such that p^3 + q^3 = 2 and p + q = 2
    use 1, 1
    constructor
    · -- Check that 1^3 + 1^3 = 2
      norm_num
    · -- Check that 1 + 1 = 2
      norm_num