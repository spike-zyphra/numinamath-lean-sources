import Mathlib

theorem inequalities_206666 (x : ℝ) : (x + 1) * (x + 2) * (x + 3) > 26 * x - 2 ↔ x > -8 ∧ x ≠ 1 := by
  constructor
  · -- Assume (x + 1) * (x + 2) * (x + 3) > 26 * x - 2, need to prove x > -8 ∧ x ≠ 1
    intro h
    have h1 : x ^ 3 + 6 * x ^ 2 - 15 * x + 8 > 0 := by
      nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x + 8), sq_nonneg (x), sq_nonneg (x + 2), sq_nonneg (x + 1), sq_nonneg (x - 1)]
    have h2 : (x + 8) * (x - 1) ^ 2 > 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 8)]
    have h3 : x + 8 > 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 8)]
    have h4 : x ≠ 1 := by
      by_contra h5
      rw [h5] at h2
      nlinarith
    constructor
    · -- x > -8
      linarith
    · -- x ≠ 1
      exact h4
  · -- Assume x > -8 ∧ x ≠ 1
    rintro ⟨h1, h2⟩
    have h3 : x ^ 3 + 6 * x ^ 2 - 15 * x + 8 > 0 := by
      have h4 : x > -8 := h1
      have h5 : x ≠ 1 := h2
      have h6 : (x - 1) ^ 2 > 0 := by
        apply pow_two_pos_of_ne_zero
        by_contra h7
        apply h5
        linarith
      have h7 : x + 8 > 0 := by linarith
      have h8 : (x + 8) * (x - 1) ^ 2 > 0 := by
        apply mul_pos
        all_goals linarith
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 8)]
    nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 2), sq_nonneg (x - 1), sq_nonneg (x + 8), sq_nonneg (x), sq_nonneg (x + 2)]