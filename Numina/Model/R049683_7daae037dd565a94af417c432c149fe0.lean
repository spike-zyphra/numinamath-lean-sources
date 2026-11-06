import Mathlib

theorem algebra_211140 (x : ℝ) :
    abs (Real.sqrt ((x - 2)^2) - 1) = x ↔ x = 1 / 2 := by
  have h1 : Real.sqrt ((x - 2) ^ 2) = |x - 2| := by
    rw [Real.sqrt_sq_eq_abs]
  rw [h1]
  constructor
  · -- Forward direction: | |x - 2| - 1 | = x implies x = 1/2
    intro h_eq
    by_cases h : |x - 2| - 1 ≥ 0
    · -- Case 1: |x-2| - 1 ≥ 0 ⟹ | |x-2| -1 | = |x-2| -1
      rw [abs_of_nonneg h] at h_eq
      by_cases h2 : x - 2 ≥ 0
      · -- Case 1b: x >= 2
        rw [abs_of_nonneg h2] at h_eq
        linarith
      · -- Case 1c: x < 2
        rw [abs_of_neg (lt_of_not_ge h2)] at h_eq
        linarith
    · -- Case 2: |x-2| - 1 < 0 ⟹ | |x-2| -1 | = 1 - |x-2|
      rw [abs_of_neg (lt_of_not_ge h)] at h_eq
      by_cases h2 : x - 2 ≥ 0
      · -- Case 2b: x ≥ 2
        rw [abs_of_nonneg h2] at h_eq
        linarith
      · -- Case 2c: x < 2
        rw [abs_of_neg (lt_of_not_ge h2)] at h_eq
        linarith [abs_nonneg (x - 2)]
  · -- Backward direction: x = 1/2 implies | |x - 2| - 1 | = x
    intro h_eq
    rw [h_eq]
    have h2 : (1 / 2 : ℝ) - 2 < 0 := by norm_num
    rw [abs_of_neg h2]
    norm_num
    all_goals norm_num [abs_of_nonneg]