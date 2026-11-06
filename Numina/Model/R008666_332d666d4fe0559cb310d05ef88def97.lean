import Mathlib

theorem algebra_9133 (x : ℝ) : x^2 - x - 6 < 0 ↔ -2 < x ∧ x < 3 := by
  constructor
  · -- Assume x^2 - x - 6 < 0, prove -2 < x ∧ x < 3
    intro h
    have h1 : x^2 - x - 6 = (x - 3) * (x + 2) := by
      ring
    rw [h1] at h
    cases mul_neg_iff.mp h with
    | inl h2 =>
      -- Case where (x - 3) > 0 ∧ (x + 2) < 0, which is impossible
      exfalso
      linarith
    | inr h2 =>
      -- Case where (x - 3) < 0 ∧ (x + 2) > 0
      constructor
      · linarith
      · linarith
  · -- Assume -2 < x ∧ x < 3, prove x^2 - x - 6 < 0
    rintro ⟨h1, h2⟩
    have h3 : x^2 - x - 6 = (x - 3) * (x + 2) := by
      ring
    rw [h3]
    have h4 : (x - 3) * (x + 2) < 0 := by
      apply mul_neg_of_neg_of_pos
      · -- Show x - 3 < 0
        linarith
      · -- Show x + 2 > 0
        linarith
    linarith