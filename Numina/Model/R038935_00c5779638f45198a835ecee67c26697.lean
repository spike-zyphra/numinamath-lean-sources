import Mathlib

open Real

theorem inequalities_265748 :
    (∀ a b : ℝ, a > 0 → b > 0 → 4 * (a ^ 2 + b ^ 2) > (a + b) ^ 2 + a * b) ∧
    IsLeast {k : ℝ | ∀ a b : ℝ, a > 0 → b > 0 → k * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 + a * b} (5 / 2) := by
  constructor
  · -- Prove the inequality 4(a^2 + b^2) > (a + b)^2 + a * b for all positive reals a, b
    intro a b ha hb
    have h1 : 4 * (a ^ 2 + b ^ 2) - ((a + b) ^ 2 + a * b) > 0 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_nonneg (a - b), sq_nonneg (a - 2 * b), sq_nonneg (2 * a - b), mul_pos ha hb]
    linarith
  · -- Prove that 5/2 is the smallest real number k
    constructor
    · -- Show that 5/2 satisfies the inequality for all positive reals
      intro a b ha hb
      have h2 : (5 / 2) * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 + a * b := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - 2 * b), sq_nonneg (2 * a - b), mul_pos ha hb, sq_nonneg (a + b)]
      linarith
    · -- Show that any k in the set must be ≥ 5/2
      intro k hk
      have h3 : ∀ a b : ℝ, a > 0 → b > 0 → k * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 + a * b := by
        simpa using hk
      have h4 := h3 1 1 (by norm_num) (by norm_num)
      linarith