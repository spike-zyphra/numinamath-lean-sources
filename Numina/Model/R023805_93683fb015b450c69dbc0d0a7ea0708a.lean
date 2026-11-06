import Mathlib

theorem algebra_322957 (x : ℝ) :
    abs (x - abs (2 * x + 1)) = 3 ↔ x = -4 / 3 ∨ x = 2 := by
  constructor
  · -- Assume abs (x - abs (2 * x + 1)) = 3, prove x = -4 / 3 ∨ x = 2
    intro h
    cases eq_or_eq_neg_of_abs_eq h with
    | inl h1 =>
      by_cases h2 : (2 * x + 1) ≥ 0
      · -- If 2x + 1 ≥ 0, then abs (2x + 1) = 2x + 1
        have h3 : abs (2 * x + 1) = 2 * x + 1 := abs_of_nonneg h2
        rw [h3] at h1
        linarith
      · -- If 2x + 1 < 0, then abs (2x + 1) = -(2x + 1)
        have h4 : abs (2 * x + 1) = -(2 * x + 1) := abs_of_neg (lt_of_not_ge h2)
        rw [h4] at h1
        linarith
    | inr h2 =>
      by_cases h3 : (2 * x + 1) ≥ 0
      · -- If 2x + 1 ≥ 0, then abs (2x + 1) = 2x + 1
        have h4 : abs (2 * x + 1) = 2 * x + 1 := abs_of_nonneg h3
        rw [h4] at h2
        right
        linarith
      · -- If 2x + 1 < 0, then abs (2x + 1) = -(2x + 1)
        have h5 : abs (2 * x + 1) = -(2 * x + 1) := abs_of_neg (lt_of_not_ge h3)
        rw [h5] at h2
        left
        linarith
  · -- Assume x = -4/3 ∨ x = 2, prove abs (x - abs (2 * x + 1)) = 3
    rintro (h | h)
    · -- Case x = -4/3
      have h1 : x = -4 / 3 := by linarith
      have h2 : abs (2 * x + 1) = -(2 * x + 1) := by
        rw [h1]
        norm_num [abs_of_nonneg, abs_of_neg]
      rw [h2]
      rw [h1]
      norm_num [abs_of_nonneg, abs_of_neg]
    · -- Case x = 2
      have h1 : x = 2 := by linarith
      have h3 : abs (2 * x + 1) = 2 * x + 1 := by
        rw [h1]
        norm_num [abs_of_nonneg, abs_of_neg]
      rw [h3]
      rw [h1]
      norm_num [abs_of_nonneg, abs_of_neg]