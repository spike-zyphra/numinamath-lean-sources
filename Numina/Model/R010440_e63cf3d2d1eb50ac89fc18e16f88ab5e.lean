import Mathlib

theorem algebra_9014 (x : ℝ) : -x^2 + 4 * x + 5 < 0 ↔ x < -1 ∨ x > 5 := by
  have h1 : -x^2 + 4 * x + 5 = -(x^2 - 4 * x - 5) := by
    ring
  rw [h1]
  have h2 : -(x^2 - 4 * x - 5) < 0 ↔ x^2 - 4 * x - 5 > 0 := by
    apply Iff.intro
    · intro h
      linarith
    · intro h
      linarith
  rw [h2]
  have h3 : x^2 - 4 * x - 5 = (x - 5) * (x + 1) := by
    ring
  rw [h3]
  constructor
  · -- Forward implication: If (x - 5) * (x + 1) > 0, then x < -1 or x > 5.
    intro h
    cases mul_pos_iff.mp h with
    | inl h1 =>
      -- Case where (x - 5) > 0 and (x + 1) > 0
      have h2 : x > 5 := by linarith
      right
      linarith
    | inr h2 =>
      -- Case where (x - 5) < 0 and (x + 1) < 0
      have h4 : x < -1 := by linarith
      left
      linarith
  · -- Backward implication: If x < -1 or x > 5, then (x - 5) * (x + 1) > 0.
    rintro (h | h)
    · -- Case x < -1
      have h1 : x - 5 < 0 := by linarith
      have h2 : x + 1 < 0 := by linarith
      apply mul_pos_iff.mpr
      right
      constructor <;> linarith
    · -- Case x > 5
      have h1 : x - 5 > 0 := by linarith
      have h2 : x + 1 > 0 := by linarith
      apply mul_pos_iff.mpr
      left
      constructor <;> linarith