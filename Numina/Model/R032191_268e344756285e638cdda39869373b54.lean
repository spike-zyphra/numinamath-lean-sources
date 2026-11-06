import Mathlib

theorem algebra_9082 (a : ℝ) :
    (∃ x : ℝ, x^2 - a * x - a ≤ -3) ↔ a ≤ -6 ∨ a ≥ 2 := by
  constructor
  · -- Assume there is a solution
    intro h
    rcases h with ⟨x, hx⟩
    have h1 : x^2 - a * x - a + 3 ≤ 0 := by linarith
    have h2 : a^2 + 4 * a - 12 ≥ 0 := by
      nlinarith [sq_nonneg (x - a / 2)]
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (a + 6), sq_nonneg (a - 2)]
  · -- Backward
    rintro (ha | ha)
    · -- Case where a ≤ -6
      have h2 : a^2 + 4 * a - 12 ≥ 0 := by nlinarith
      use (a + Real.sqrt (a^2 + 4 * a - 12)) / 2
      nlinarith [Real.sqrt_nonneg (a^2 + 4 * a - 12), Real.sq_sqrt (show 0 ≤ a^2 + 4 * a - 12 by nlinarith)]
    · -- Case where a ≥ 2
      have h2 : a^2 + 4 * a - 12 ≥ 0 := by nlinarith
      use (a + Real.sqrt (a^2 + 4 * a - 12)) / 2
      nlinarith [Real.sqrt_nonneg (a^2 + 4 * a - 12), Real.sq_sqrt (show 0 ≤ a^2 + 4 * a - 12 by nlinarith)]