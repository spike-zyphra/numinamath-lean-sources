import Mathlib

open Real

theorem inequalities_258170 :
    (∀ a b c d : ℝ, a^2 + b^2 + c^2 + d^2 = 4 → (a + 2) * (b + 2) ≥ c * d) ∧
    ∃ a b c d : ℝ, a^2 + b^2 + c^2 + d^2 = 4 ∧ (a + 2) * (b + 2) = c * d := by
  constructor
  · -- First part: Prove inequality holds
    intro a b c d h
    nlinarith [sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (a + b + 2), sq_nonneg (c + d), sq_nonneg (a - b), sq_nonneg (c - d)]
  · -- Second part: Prove existance of 4 numbers where equality holds
    use -1, -1, 1, 1
    constructor
    · -- Show the constraint is satisfied
      norm_num
    · -- Show equality holds
      norm_num