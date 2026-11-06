import Mathlib

theorem algebra_297703 (x : ℝ) :
    x = abs (x - abs (x - 6)) ↔ x = 2 ∨ x = 6 := by
  constructor
  · -- Assume x = abs (x - abs (x - 6)), prove x = 2 ∨ x = 6
    intro h
    by_cases h1 : x ≥ 6
    · -- If x ≥ 6
      have h2 : abs (x - 6) = x - 6 := by
        rw [abs_of_nonneg]
        linarith
      have h3 : abs (x - abs (x - 6)) = 6 := by
        rw [h2]
        have h4 : x - (x - 6) = 6 := by
          linarith
        rw [h4]
        norm_num
      have h4 : x = 6 := by
        linarith [h, h3]
      right
      exact h4
    · -- If x < 6
      have h1' : abs (x - 6) = 6 - x := by
        rw [abs_of_neg]
        linarith
        all_goals linarith
      have h2 : x - abs (x - 6) = 2 * x - 6 := by
        rw [h1']
        all_goals linarith
      by_cases h3 : 2 * x - 6 ≥ 0
      · -- If 2 * x - 6 ≥ 0, then abs (2 * x - 6) = 2 * x - 6
        have h4 : abs (x - abs (x - 6)) = 2 * x - 6 := by
          rw [h2]
          rw [abs_of_nonneg h3]
        have h5 : x = 2 * x - 6 := by
          linarith [h, h4]
        have h6 : x = 6 := by
          linarith [h5]
        linarith [h1, h6]
      · -- If 2 * x - 6 < 0, then abs (2 * x - 6) = -(2 * x - 6)
        have h4 : abs (x - abs (x - 6)) = - (2 * x - 6) := by
          rw [h2]
          rw [abs_of_neg]
          linarith
          all_goals linarith
        have h5 : x = - (2 * x - 6) := by
          linarith [h, h4]
        have h6 : x = 2 := by
          linarith [h5]
        left
        exact h6
  · -- Assume x = 2 ∨ x = 6, prove x = abs (x - abs (x - 6))
    rintro (h | h)
    · -- If x = 2
      rw [h]
      norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- If x = 6
      rw [h]
      norm_num [abs_of_nonneg, abs_of_nonpos]