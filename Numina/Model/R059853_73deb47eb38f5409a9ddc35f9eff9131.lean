import Mathlib

theorem inequalities_121450 (x y : ℝ) : x^2 + 2 * y^2 + 1 / 2 ≤ x * (2 * y + 1) ↔ x = 1 ∧ y = 1 / 2 := by

  constructor
  · -- Forward implication: from inequality to (x, y) = (1, 1/2).
    intro h

    have h1 : (x - (1 + 2 * y) / 2) ^ 2 + (y - 1 / 2) ^ 2 ≤ 0 := by
      nlinarith

    -- Now we know that both (x - (1 + 2y)/2)^2 = 0 and (y - 1/2)^2 = 0 because squares are non-negative.

    have hy1 : (y - 1 / 2) ^ 2 = 0 := by
      linarith [sq_nonneg (x - (1 + 2 * y) / 2), sq_nonneg (y - 1 / 2)]

    -- From (y - 1/2)^2 = 0, we can deduce y = 1/2.

    have hy : y = 1 / 2 := by
      nlinarith

    -- Substituting y = 1/2 into the original equation to solve for x.

    have hx : x = 1 := by
      rw [hy] at h1
      nlinarith [sq_nonneg (x - 1)]

    -- Concluding that (x, y) = (1, 1/2).

    exact ⟨hx, hy⟩

  · -- Backward implication: from (x, y) = (1, 1/2) to the inequality.

    rintro ⟨rfl, rfl⟩

    -- Verify the inequality at (1, 1/2).

    norm_num