import Mathlib

theorem algebra_2291 (x : ℝ) : abs (x ^ 2 - 1) = x ^ 2 - 1 ↔ x ≤ -1 ∨ x ≥ 1 := by
  constructor
  · -- Forward direction: abs (x ^ 2 - 1) = x ^ 2 - 1 → x ≤ -1 ∨ x ≥ 1
    intro h
    have h1 : x^2 - 1 ≥ 0 := by
      by_cases h2 : x^2 - 1 ≥ 0
      · -- In this case, abs (x ^ 2 - 1) = x ^ 2 - 1, so h is trivial
        rw [abs_of_nonneg h2] at h
        linarith
      · -- Case where x^2 - 1 < 0, so abs (x ^ 2 - 1) = -(x ^ 2 - 1)
        have h2' : x^2 - 1 < 0 := by linarith
        rw [abs_of_neg h2'] at h
        linarith
    have h2 : x^2 ≥ 1 := by linarith
    have h3 : (x ≤ -1) ∨ (x ≥ 1) := by
      by_cases h4 : x ≥ 0
      · -- Case where x ≥ 0
        have h5 : x ≥ 1 := by
          nlinarith
        right
        exact h5
      · -- Case where x < 0
        have h4' : x < 0 := by linarith
        have h5 : x ≤ -1 := by
          nlinarith
        left
        exact h5
    exact h3
  · -- Backward direction: x ≤ -1 ∨ x ≥ 1 → abs (x ^ 2 - 1) = x ^ 2 - 1
    rintro (h | h)
    · -- Case x ≤ -1
      have h1 : x^2 ≥ 1 := by
        nlinarith
      have h2 : x^2 - 1 ≥ 0 := by
        linarith
      rw [abs_of_nonneg h2]
    · -- Case x ≥ 1
      have h1 : x^2 ≥ 1 := by
        nlinarith
      have h2 : x^2 - 1 ≥ 0 := by
        linarith
      rw [abs_of_nonneg h2]