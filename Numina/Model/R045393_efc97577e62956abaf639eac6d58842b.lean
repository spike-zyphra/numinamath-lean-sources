import Mathlib

theorem algebra_9005 (x : ℝ) : abs (2 - 3 * x) ≥ 4 ↔ x ≤ -2 / 3 ∨ x ≥ 2 := by
  constructor
  · -- Forward direction: if abs (2 - 3 * x) ≥ 4 then x ≤ -2 / 3 ∨ x ≥ 2
    intro h
    cases abs_choice (2 - 3 * x) with
    | inl h1 =>
      have h2 : x ≤ -2 / 3 := by
        linarith
      left
      exact h2
    | inr h2 =>
      right
      linarith
  · -- Backward direction: if x ≤ -2 / 3 ∨ x ≥ 2 then abs (2 - 3 * x) ≥ 4
    rintro (h | h)
    · -- Case x ≤ -2 / 3
      have h1 : 2 - 3 * x ≥ 4 := by
        linarith
      rw [abs_of_nonneg (by linarith)]
      linarith
    · -- Case x ≥ 2
      have h1 : 2 - 3 * x ≤ -4 := by
        linarith
      rw [abs_of_nonpos (by linarith)]
      linarith