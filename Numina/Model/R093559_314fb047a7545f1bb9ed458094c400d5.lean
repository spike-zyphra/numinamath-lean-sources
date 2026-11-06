import Mathlib

theorem algebra_245802 (x : ℝ) :
    0 < (3 - 3 * x + x ^ 2) / (2 + 3 * x - 5 * x ^ 2) ↔
    -2 / 5 < x ∧ x < 1 := by
  constructor
  · -- Assume 0 < (3 - 3 * x + x ^ 2) / (2 + 3 * x - 5 * x ^ 2), prove -2/5 < x ∧ x < 1
    intro h
    have h5 : (3 - 3 * x + x ^ 2) > 0 := by
      nlinarith [sq_nonneg (x - 3 / 2)]
    have h2 : (2 + 3 * x - 5 * x ^ 2) > 0 := by
      apply (div_pos_iff_of_pos_left h5).mp at h
      nlinarith
    have h3 : -2 / 5 < x := by
      nlinarith [sq_nonneg (x - -2 / 5), sq_nonneg (x - 1)]
    have h4 : x < 1 := by
      nlinarith [sq_nonneg (x - -2 / 5), sq_nonneg (x - 1)]
    exact ⟨h3, h4⟩
  · -- Assume -2/5 < x ∧ x < 1, prove 0 < (3 - 3 * x + x ^ 2) / (2 + 3 * x - 5 * x ^ 2)
    rintro ⟨h1, h2⟩
    have h5 : (3 - 3 * x + x ^ 2) > 0 := by
      nlinarith [sq_nonneg (x - 3 / 2)]
    have h2_pos : (2 + 3 * x - 5 * x ^ 2) > 0 := by
      nlinarith [sq_nonneg (x - -2 / 5), sq_nonneg (x - 1)]
    have h6 : (3 - 3 * x + x ^ 2) / (2 + 3 * x - 5 * x ^ 2) > 0 := by
      apply div_pos
      all_goals nlinarith [sq_nonneg (x ^ 2 - 3 * x + 3), sq_nonneg (x - -2 / 5), sq_nonneg (x - 1)]
    linarith