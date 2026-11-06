import Mathlib

theorem algebra_9290 : IsGreatest {x : ℝ | ∃ a b c : ℝ, a^2 + b^2 + c^2 = 3 ∧ 2 * a * b + 3 * c = x} (21 / 4) := by
  constructor
  · -- Show that 21/4 is achievable
    use Real.sqrt 6 / 4, Real.sqrt 6 / 4, 3 / 2
    constructor
    · -- Check that a^2 + b^2 + c^2 = 3
      have h1 : (Real.sqrt 6 / 4 : ℝ) ^ 2 = (6 / 16 : ℝ) := by
        calc
          (Real.sqrt 6 / 4 : ℝ) ^ 2
            = (Real.sqrt 6 ^ 2) / 16 := by ring_nf
          _ = (6 / 16 : ℝ) := by
            rw [Real.sq_sqrt]
            all_goals norm_num
      nlinarith [h1]
    · -- Check that 2 * a * b + 3 * c = 21 / 4
      have h1 : (Real.sqrt 6 / 4 : ℝ) ^ 2 = (6 / 16 : ℝ) := by
        calc
          (Real.sqrt 6 / 4 : ℝ) ^ 2
            = (Real.sqrt 6 ^ 2) / 16 := by ring_nf
          _ = (6 / 16 : ℝ) := by
            rw [Real.sq_sqrt]
            all_goals norm_num
      nlinarith [h1]
  · -- Show that 21/4 is indeed the greatest element in the set
    intro x hx
    rcases hx with ⟨a, b, c, h1, h2⟩
    nlinarith [sq_nonneg (a - b), sq_nonneg (c - 3 / 2), sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a ^ 2 + b ^ 2 - 3 / 4)]