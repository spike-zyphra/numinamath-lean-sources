import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_84150 :
  (∀ a b c d : ℝ, a^2 + b^2 + c^2 + d^2 = 4 → (a + 2) * (b + 2) ≥ c * d) ∧
  ∃ a b c d : ℝ, a^2 + b^2 + c^2 + d^2 = 4 ∧ (a + 2) * (b + 2) = c * d := by
  constructor
  · -- First part: prove the inequality holds for all real numbers satisfying the constraint
    intros a b c d h_eq
    nlinarith [sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (a + b + 2), sq_nonneg (c + d), sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a + b - c - d)]
  · -- Second part: provide four real numbers where equality holds
    use -1, -1, 1, 1
    constructor
    · -- Show that the sum of squares equals 4
      norm_num
    · -- Show that (a + 2)(b + 2) = c * d at equality
      norm_num