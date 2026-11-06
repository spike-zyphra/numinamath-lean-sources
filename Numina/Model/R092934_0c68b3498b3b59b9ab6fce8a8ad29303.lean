import Mathlib

theorem algebra_256285 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 2 * a + 4 * b + 8 * c = 16) :
    a * b * c ≤ 64 / 27 ∧ ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 2 * a + 4 * b + 8 * c = 16 ∧ a * b * c = 64 / 27 := by
  constructor
  · -- We need to prove $abc \leq 64/27$
    nlinarith [sq_nonneg (a - 8 / 3), sq_nonneg (b - 4 / 3), sq_nonneg (c - 2 / 3),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      sq_nonneg (a - 2 * b), sq_nonneg (b - 2 * c), sq_nonneg (a - 4 * c)]
  · -- We need to prove the existence of a, b, c where the maximum is attained
    use 8 / 3, 4 / 3, 2 / 3
    constructor
    · -- Show a > 0
      norm_num
    constructor
    · -- Show b > 0
      norm_num
    constructor
    · -- Show c > 0
      norm_num
    constructor
    · -- Verify the constraint
      norm_num
    · -- Verify the product equals 64/27
      norm_num