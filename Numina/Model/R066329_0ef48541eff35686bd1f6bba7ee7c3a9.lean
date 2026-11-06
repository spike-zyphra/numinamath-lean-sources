import Mathlib

theorem algebra_1179 (x : ℝ) :
  abs (x - abs (2 * x + 1)) = 3 ↔ x = 2 ∨ x = -4 / 3 := by
  constructor
  · -- Forward direction: if abs (x - abs (2 * x + 1)) = 3, then x = 2 or x = -4/3
    intro h
    cases eq_or_eq_neg_of_abs_eq h with
    | inl h1 =>
      by_cases h2 : 2 * x + 1 ≥ 0
      · -- If 2x + 1 ≥ 0, then |2x + 1| = 2x + 1
        have h3 : abs (2 * x + 1) = 2 * x + 1 := abs_of_nonneg h2
        rw [h3] at h1
        have h4 : x = -4 := by linarith
        linarith
      · -- If 2x + 1 < 0, then |2x + 1| = -(2x + 1)
        have h2' : 2 * x + 1 < 0 := by linarith
        have h3 : abs (2 * x + 1) = -(2 * x + 1) := abs_of_neg h2'
        rw [h3] at h1
        have h4 : x = 2 / 3 := by linarith
        linarith
    | inr h2 =>
      by_cases h3 : 2 * x + 1 ≥ 0
      · -- If 2x + 1 ≥ 0, then |2x + 1| = 2x + 1
        have h4 : abs (2 * x + 1) = 2 * x + 1 := abs_of_nonneg h3
        rw [h4] at h2
        have h5 : x = 2 := by linarith
        left
        exact h5
      · -- If 2x + 1 < 0, then |2x + 1| = -(2x + 1)
        have h3' : 2 * x + 1 < 0 := by linarith
        have h4 : abs (2 * x + 1) = -(2 * x + 1) := abs_of_neg h3'
        rw [h4] at h2
        have h5 : x = -4 / 3 := by linarith
        right
        exact h5
  · -- Backward direction: if x = 2 or x = -4/3, then abs (x - abs (2 * x + 1)) = 3
    rintro (h | h)
    · -- If x = 2
      rw [h]
      norm_num [abs_of_nonneg]
    · -- If x = -4/3
      rw [h]
      norm_num [abs_of_nonneg, abs_of_neg]