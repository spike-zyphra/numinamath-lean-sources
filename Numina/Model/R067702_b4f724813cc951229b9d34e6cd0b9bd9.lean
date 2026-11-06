import Mathlib

theorem algebra_172281 (x : ℝ) :
    abs (abs (x - 1) + 2) - 3 = -2 * x - 4 ↔ x = -4 := by
  constructor
  · -- Assume abs (abs (x - 1) + 2) - 3 = -2 * x - 4, prove x = -4
    intro h
    have eq1 : abs (abs (x - 1) + 2) = abs (x - 1) + 2 := by
      apply abs_of_nonneg
      have h2 : abs (x - 1) + 2 ≥ 0 := by
        linarith [abs_nonneg (x - 1)]
      linarith
    rw [eq1] at h
    by_cases h2 : x - 1 ≥ 0
    · -- Case x - 1 ≥ 0, i.e., x ≥ 1
      have h2' : abs (x - 1) = x - 1 := abs_of_nonneg h2
      rw [h2'] at h
      linarith
    · -- Case x - 1 < 0, i.e., x < 1
      have h3 : abs (x - 1) = -(x - 1) := abs_of_neg (lt_of_not_ge h2)
      rw [h3] at h
      linarith
  · -- Assume x = -4, prove abs (abs (x - 1) + 2) - 3 = -2 * x - 4
    intro h
    rw [h]
    norm_num [abs_of_nonneg, abs_of_neg]