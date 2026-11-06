import Mathlib

theorem algebra_1415 (x : ℝ) (hx : 2 * |x + 1| ≠ 0) :
    (|x - 3| - |x + 1|) / (2 * |x + 1|) = 1 ↔ x = -3 ∨ x = 0 := by
  constructor
  · -- Assume (|x - 3| - |x + 1|) / (2 * |x + 1|) = 1, prove x = -3 ∨ x = 0.
    intro h
    have h1 : |x + 1| ≠ 0 := by
      by_contra h2
      have : 2 * |x + 1| = 0 := by
        linarith [h2]
      contradiction
    have h2 : |x - 3| - |x + 1| = 2 * |x + 1| := by
      have : (|x - 3| - |x + 1|) / (2 * |x + 1|) = 1 := by
        simpa using h
      field_simp [show 2 * |x + 1| ≠ 0 by tauto] at this ⊢
      linarith [this]
    have h3 : |x - 3| = 3 * |x + 1| := by linarith
    by_cases h4 : x ≥ 3
    · -- Case 1: x ≥ 3
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h3
      nlinarith
    · -- Case 2: x < 3
      by_cases h5 : x ≥ -1
      · -- Case 2a: -1 ≤ x < 3
        rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h3
        have : x = 0 := by linarith
        right
        linarith
      · -- Case 2b: x < -1
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h3
        have : x = -3 := by linarith
        left
        linarith
  · -- Assume x = -3 ∨ x = 0, prove (|x - 3| - |x + 1|) / (2 * |x + 1|) = 1.
    rintro (h | h)
    · -- Case 1: x = -3
      rw [h]
      norm_num [abs]
    · -- Case 2: x = 0
      rw [h]
      norm_num [abs]