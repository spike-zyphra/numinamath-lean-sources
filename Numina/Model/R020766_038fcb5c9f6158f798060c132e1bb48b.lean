import Mathlib

theorem algebra_303842 :
    IsGreatest {x | ∃ a b c d : ℝ, x = a * b + b * c + c * d + d * a + a * c + 4 * b * d ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1} (5 / 2) := by
  constructor
  · -- Show 5/2 is in the set
    use Real.sqrt (1 / 10), 2 * Real.sqrt (1 / 10), Real.sqrt (1 / 10), 2 * Real.sqrt (1 / 10)
    constructor
    · -- Show that the value of the expression is 5/2
      nlinarith [Real.sqrt_nonneg (1 / 10), Real.sq_sqrt (show (0 : ℝ) ≤ (1 / 10) by norm_num)]
    · -- Show that the constraint is satisfied
      nlinarith [Real.sqrt_nonneg (1 / 10), Real.sq_sqrt (show (0 : ℝ) ≤ (1 / 10) by norm_num)]
  · -- Show that 5/2 is greatest
    intro x hx
    rcases hx with ⟨a, b, c, d, h_eq, h_eq1⟩
    nlinarith [sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a + 2 * b - c - 2 * d), sq_nonneg (b - c - d + a), 
      sq_nonneg (a + c - 2 * (b + d)), sq_nonneg (2 * (a - c) - (b - d)), 
      sq_nonneg (a + c + 2 * (b - d)), sq_nonneg (2 * (a + c) - (b + d)), 
      mul_self_nonneg (a - c), mul_self_nonneg (b - d), 
      mul_self_nonneg (a + c), mul_self_nonneg (b + d)]