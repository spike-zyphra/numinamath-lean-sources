import Mathlib

theorem algebra_9132 (x : ℝ) : (2:ℝ)^(|x - 2| + |x - 4|) > 2^6 ↔ x < 0 ∨ x > 6 := by
  constructor
  · -- Assume (2:ℝ)^(|x - 2| + |x - 4|) > 2^6, prove x < 0 ∨ x > 6
    intro h
    have h1 : |x - 2| + |x - 4| > (6 : ℝ) := by
      by_contra h2
      push_neg at h2
      have h2' : (2 : ℝ) ^ (|x - 2| + |x - 4|) ≤ (2 : ℝ) ^ (6 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        all_goals linarith
      linarith
    by_cases h2 : x ≥ 4
    · -- x ≥ 4
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h1
      right
      linarith
    · -- x < 4
      by_cases h3 : x ≥ 2
      · -- 2 ≤ x < 4
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)] at h1
        exfalso
        linarith
      · -- x < 2
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h1
        left
        linarith
  · -- Assume x < 0 ∨ x > 6, prove (2:ℝ)^(|x - 2| + |x - 4|) > 2^6
    rintro (h | h)
    · -- x < 0
      have h1 : |x - 2| + |x - 4| > (6 : ℝ) := by
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        all_goals linarith
      have h2 : (2 : ℝ) ^ (|x - 2| + |x - 4|) > (2 : ℝ) ^ (6 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt
        all_goals linarith
      linarith
    · -- x > 6
      have h1 : |x - 2| + |x - 4| > (6 : ℝ) := by
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        all_goals linarith
      have h2 : (2 : ℝ) ^ (|x - 2| + |x - 4|) > (2 : ℝ) ^ (6 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt
        all_goals linarith
      linarith