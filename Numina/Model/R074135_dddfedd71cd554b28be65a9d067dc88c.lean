import Mathlib

theorem algebra_11486 (x : ℝ) : 5 * x - 1 < (x + 1)^2 ∧ (x + 1)^2 < 7 * x - 3 ↔ 2 < x ∧ x < 4 := by
  constructor
  · -- Assume left side, prove right side
    rintro ⟨h₁, h₂⟩
    constructor
    · -- Assume $5 * x - 1 < (x + 1)^2$, prove $2 < x$
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 4)]
    · -- Assume $(x + 1)^2 < 7 * x - 3$, prove $x < 4$
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 4)]
  · -- Assume right side, prove left side
    rintro ⟨h₁, h₂⟩
    constructor
    · -- Assume $2 < x$ prove $5 * x - 1 < (x + 1)^2$
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 4)]
    · -- Assume $x < 4$ prove $(x + 1)^2 < 7 * x - 3$
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 4)]