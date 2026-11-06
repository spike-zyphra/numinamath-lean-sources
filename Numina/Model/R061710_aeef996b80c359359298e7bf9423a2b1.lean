import Mathlib

theorem algebra_174280 (x : ℝ) : abs (x - 1) + abs (x - 5) = 4 ↔ 1 ≤ x ∧ x ≤ 5 := by
  constructor
  · -- Forward direction: If abs (x - 1) + abs (x - 5) = 4, then 1 ≤ x ∧ x ≤ 5
    intro h_eq
    by_cases h1 : x ≥ 1
    · -- Case x ≥ 1
      rw [abs_of_nonneg (by linarith)] at h_eq
      by_cases h2 : x ≥ 5
      · -- Case x ≥ 5
        rw [abs_of_nonneg (by linarith)] at h_eq
        constructor
        · linarith
        · linarith
      · -- Case 1 ≤ x < 5
        rw [abs_of_neg (by linarith)] at h_eq
        constructor
        · linarith
        · linarith
    · -- Case x < 1
      rw [abs_of_neg (by linarith)] at h_eq
      by_cases h2 : x ≥ 5
      · -- Case x ≥ 5 and x < 1 (impossible)
        rw [abs_of_nonneg (by linarith)] at h_eq
        constructor
        · linarith
        · linarith
      · -- Case x < 1 and x < 5
        rw [abs_of_neg (by linarith)] at h_eq
        constructor
        · linarith
        · linarith
  · -- Backward direction: If 1 ≤ x ∧ x ≤ 5, then abs (x - 1) + abs (x - 5) = 4
    rintro ⟨h1, h2⟩
    have h3 : x - 1 ≥ 0 := by linarith
    have h4 : x - 5 ≤ 0 := by linarith
    rw [abs_of_nonneg h3, abs_of_nonpos h4]
    linarith