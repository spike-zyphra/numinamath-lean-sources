import Mathlib

theorem algebra_308808 : IsGreatest {e : ℝ | ∃a b c d, a + b + c + d + e = 8 ∧ a^2 + b^2 + c^2 + d^2 + e^2 = 16} (16/5) := by
  constructor
  · -- Show 16/5 is in the set.
    use 6 / 5, 6 / 5, 6 / 5, 6 / 5
    constructor
    · -- Check that the sum is 8.
      norm_num
    · -- Check that the sum of squares is 16.
      norm_num
  · -- Show there is no greater element in the set.
    intro e he
    rcases he with ⟨a, b, c, d, h1, h2⟩
    have h3 : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
      nlinarith [sq_nonneg (a + b + c + d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
    have h4 : a + b + c + d = 8 - e := by linarith
    have h5 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 16 - e ^ 2 := by linarith 
    rw [h4, h5] at h3
    nlinarith [sq_nonneg (e - 16 / 5)]