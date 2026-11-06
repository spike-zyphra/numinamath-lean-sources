import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_276741 (x : ℝ) (hx : 5 - x + 6 * x ^ 2 ≠ 0) :
    (2 + 7 * x - 15 * x ^ 2) / (5 - x + 6 * x ^ 2) > 0 ↔
    -1 / 5 < x ∧ x < 2 / 3 := by
  have h1 : 5 - x + 6 * x^2 > 0 := by
    nlinarith [sq_nonneg (x + 1 / 12), sq_nonneg (x - 2 / 3), sq_nonneg (x + 1 / 5)]
  have h2 : (2 + 7 * x - 15 * x ^ 2) / (5 - x + 6 * x ^ 2) > 0 ↔ (2 + 7 * x - 15 * x ^ 2) > 0 := by
    apply Iff.intro
    · -- Assume (2 + 7 * x - 15 * x ^ 2) / (5 - x + 6 * x ^ 2) > 0, need to show 2 + 7 * x - 15 * x ^ 2 > 0
      intro h
      apply (div_pos_iff_of_pos_right h1).mp at h
      linarith
    · -- Assume 2 + 7 * x - 15 * x ^ 2 > 0, need to show (2 + 7 * x - 15 * x ^ 2) / (5 - x + 6 * x ^ 2) > 0
      intro h
      apply div_pos 
      all_goals linarith
  rw [h2]
  constructor
  · -- Assume 2 + 7 * x - 15 * x^2 > 0, prove -1/5 < x ∧ x < 2/3
    intro h
    constructor
    · -- Prove -1/5 < x
      nlinarith [sq_nonneg (x + 1 / 5), sq_nonneg (x - 2 / 3)]
    · -- Prove x < 2/3
      nlinarith [sq_nonneg (x + 1 / 5), sq_nonneg (x - 2 / 3)]
  · -- Assume -1/5 < x ∧ x < 2/3, prove 2 + 7 * x - 15 * x^2 > 0
    rintro ⟨h1, h2⟩
    nlinarith [sq_nonneg (x + 1 / 5), sq_nonneg (x - 2 / 3)]