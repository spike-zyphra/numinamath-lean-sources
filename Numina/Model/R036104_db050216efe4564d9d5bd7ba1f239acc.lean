import Mathlib

theorem algebra_96163 : IsGreatest {e | ∃(a b c d : ℝ), a + b + c + d + e = 8 ∧ a^2 + b^2 + c^2 + d^2 + e^2 = 16} (16/5) := by
  constructor
  · -- Show that 16/5 is in the set.
    use 6/5, 6/5, 6/5, 6/5
    constructor
    · -- Check the first constraint: a + b + c + d + e = 8
      norm_num
    · -- Check the second constraint: a^2 + b^2 + c^2 + d^2 + e^2 = 16
      norm_num
  · -- Show that if e is in the set, then e ≤ 16/5.
    intro e he
    rcases he with ⟨a, b, c, d, h1, h2⟩
    -- We have two equations: 
    -- 1. a + b + c + d + e = 8 
    -- 2. a^2 + b^2 + c^2 + d^2 + e^2 = 16 
    -- From the first, we can express the sum of the first four variables:
    have h4 : (a + b + c + d) = (8 - e) := by linarith 
    -- From the second, we can express the sum of their squares:
    have h5 : (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) = (16 - e ^ 2) := by linarith 
    -- Now we have the sum and the sum of squares of the 4 variables. Using the inequality from Cauchy:
    have h3 : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by 
      linarith [sq_nonneg (a + b + c + d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
    rw [h4, h5] at h3
    nlinarith