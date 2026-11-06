import Mathlib

theorem algebra_315157 (a b x : ℝ) (ha : 0 < a) (hb : b < 0) :
    abs (x - a) + abs (x - b) = a - b ↔ b ≤ x ∧ x ≤ a := by
  constructor
  · -- Forward direction: if |x-a| + |x-b| = a - b, then b ≤ x ∧ x ≤ a
    intro h
    have h1 : a - b > 0 := by linarith
    by_cases h2 : x ≥ a
    · -- Case x ≥ a
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
      constructor
      · linarith
      · linarith
    · -- Case x < a
      by_cases h3 : x ≤ b
      · -- Case x ≤ b
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h
        constructor
        · linarith
        · linarith
      · -- Case b < x < a
        have h4 : x > b := by nlinarith
        have h5 : x < a := by nlinarith
        rw [abs_of_neg (by linarith), abs_of_pos (by linarith)] at h
        constructor
        · linarith
        · linarith
  · -- Backward direction: if b ≤ x ∧ x ≤ a, then |x-a| + |x-b| = a - b
    rintro ⟨h1, h2⟩
    have h3 : x - a ≤ 0 := by linarith
    have h4 : x - b ≥ 0 := by linarith
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    all_goals linarith