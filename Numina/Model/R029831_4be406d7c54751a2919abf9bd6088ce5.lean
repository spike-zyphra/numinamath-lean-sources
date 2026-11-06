import Mathlib

theorem algebra_12648 (a : ℝ) :
    (a ^ 2 - 10 * a + 21 ≤ 0) ↔ a ≤ 7 ∧ a ≥ 3 := by
  constructor
  · -- Forward implication: if a^2 - 10 * a + 21 ≤ 0, then 3 ≤ a ≤ 7
    intro h
    constructor
    · -- Prove a ≤ 7
      nlinarith [sq_nonneg (a - 3), sq_nonneg (a - 7)]
    · -- Prove a ≥ 3
      nlinarith [sq_nonneg (a - 3), sq_nonneg (a - 7)]
  · -- Backward implication: if 3 ≤ a ≤ 7, then a^2 - 10 * a + 21 ≤ 0
    rintro ⟨h1, h2⟩
    nlinarith