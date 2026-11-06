import Mathlib

theorem algebra_9195 (x : ℝ) : 2 * (x ^ 2 - x) < 4 ↔ -1 < x ∧ x < 2 := by
  constructor
  · -- Assume 2 * (x ^ 2 - x) < 4, prove -1 < x ∧ x < 2
    intro h
    have h1 : x^2 - x - 2 < 0 := by linarith
    have h2 : x^2 - x - 2 = (x - 2) * (x + 1) := by ring
    rw [h2] at h1
    cases mul_neg_iff.mp h1 with
    | inl h3 =>
      linarith -- This case is impossible, as it would require x > 2 and x < -1
    | inr h4 =>
      constructor
      · linarith
      · linarith
  · -- Assume -1 < x ∧ x < 2, prove 2 * (x ^ 2 - x) < 4
    rintro ⟨h1, h2⟩
    have h3 : x + 1 > 0 := by linarith
    have h4 : x - 2 < 0 := by linarith
    nlinarith