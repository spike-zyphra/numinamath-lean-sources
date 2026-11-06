import Mathlib

theorem algebra_22524 : 
    IsGreatest {a : ℝ | ∃(b c : ℝ), a + 3 * b + 4 * c = 25 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 25} (25 / 13) := by
  constructor 
  · -- Show that 25/13 is achievable with b = 36/13 and c = 48/13
    use 36 / 13, 48 / 13 
    constructor 
    · -- Check that a + 3 * b + 4 * c = 25
      norm_num 
    · -- Check that a ^ 2 + b ^ 2 + c ^ 2 = 25
      norm_num 
  · -- Show that any a in the set is ≤ 25/13
    intro a ha 
    rcases ha with ⟨b, c, h1, h2⟩
    nlinarith [sq_nonneg (b - 36 / 13), sq_nonneg (c - 48 / 13), 
      sq_nonneg (3 * b - 4 * c), sq_nonneg (a - 25 / 13), 
        mul_nonneg (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]