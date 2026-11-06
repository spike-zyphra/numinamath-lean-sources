import Mathlib

theorem inequalities_253572 (x : ℝ) : abs (x - 6) < x ^ 2 - 5 * x + 9 ↔ x < 1 ∨ x > 3 := by
  constructor
  · -- Forward direction: abs (x - 6) < x ^ 2 - 5 * x + 9 implies x < 1 ∨ x > 3
    intro h
    by_cases h1 : x - 6 ≥ 0
    · -- Case 1: x - 6 ≥ 0, so abs (x - 6) = x - 6
      rw [abs_of_nonneg h1] at h
      have h2 : x ≥ 6 := by linarith
      have h3 : x > 3 := by nlinarith
      right
      nlinarith
    · -- Case 2: x - 6 < 0, so abs (x - 6) = 6 - x
      rw [abs_of_neg (lt_of_not_ge h1)] at h
      have h2 : x < 6 := by nlinarith
      have h3 : (x - 1) * (x - 3) > 0 := by 
        nlinarith
      have : x < 1 ∨ x > 3 := by
        by_contra h5
        push_neg at h5
        have h4 : (x - 1) * (x - 3) ≤ 0 := by
          nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 3), h5.1, h5.2]
        nlinarith
      tauto
  · -- Backward direction: x < 1 ∨ x > 3 implies abs (x - 6) < x ^ 2 - 5 * x + 9
    rintro (h | h)
    · -- Case 1: x < 1
      by_cases h1 : x - 6 ≥ 0
      · -- Case 1a: x - 6 ≥ 0 and x < 1
        rw [abs_of_nonneg h1]
        nlinarith
      · -- Case 1b: x - 6 < 0 and x < 1
        rw [abs_of_neg (lt_of_not_ge h1)]
        nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 1)]
    · -- Case 2: x > 3
      by_cases h1 : x - 6 ≥ 0
      · -- Case 2a: x - 6 ≥ 0 and x > 3
        rw [abs_of_nonneg h1]
        nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 6)]
      · -- Case 2b: x - 6 < 0 and x > 3
        rw [abs_of_neg (lt_of_not_ge h1)]
        nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 1)]