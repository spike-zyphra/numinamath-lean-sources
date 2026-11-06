import Mathlib

theorem algebra_103535 (x : ℝ) :
    abs (abs (x) - 1) + abs (abs (x) + 2) = 3 ↔ -1 ≤ x ∧ x ≤ 1 := by
  constructor
  · -- Assume abs (abs (x) - 1) + abs (abs (x) + 2) = 3, prove -1 ≤ x ∧ x ≤ 1
    intro h
    have h1 : abs (abs (x) + 2) = abs (x) + 2 := by
      apply abs_of_nonneg
      linarith [abs_nonneg (x), abs_nonneg (x)]
    rw [h1] at h
    have h2 : abs (abs (x) - 1) + abs (x) = 1 := by linarith
    by_cases h3 : abs (x) - 1 ≥ 0
    · -- Case abs (x) - 1 ≥ 0 (i.e., abs (x) ≥ 1)
      rw [abs_of_nonneg h3] at h2
      have h4 : abs (x) = 1 := by linarith
      constructor
      · -- Prove -1 ≤ x
        cases eq_or_eq_neg_of_abs_eq h4 with
        | inl h5 =>
          linarith
        | inr h5 =>
          linarith
      · -- Prove x ≤ 1
        cases eq_or_eq_neg_of_abs_eq h4 with
        | inl h5 =>
          linarith
        | inr h5 =>
          linarith
    · -- Case abs (x) - 1 < 0 (i.e., abs (x) < 1)
      have h4 : abs (x) < 1 := by linarith
      rw [abs_of_neg (lt_of_not_ge h3)] at h2
      constructor
      · -- Show -1 ≤ x
        cases abs_cases x with
        | inl h9 =>
          linarith
        | inr h9 =>
          linarith
      · -- Show x ≤ 1
        cases abs_cases x with
        | inl h9 =>
          linarith
        | inr h9 =>
          linarith
  · -- Assume -1 ≤ x ∧ x ≤ 1, prove abs (abs (x) - 1) + abs (abs (x) + 2) = 3
    rintro ⟨h1, h2⟩
    have h3 : abs (x) ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith
    have h1' : abs (abs (x) + 2) = abs (x) + 2 := by
      apply abs_of_nonneg
      linarith [abs_nonneg (x), abs_nonneg (x)]
    have h4 : abs (abs (x) - 1) = 1 - abs (x) := by
      rw [abs_of_nonpos (by linarith [abs_nonneg (x), h3]), neg_sub]
      all_goals linarith [abs_nonneg (x)]
    rw [h1', h4]
    linarith [abs_nonneg (x)]