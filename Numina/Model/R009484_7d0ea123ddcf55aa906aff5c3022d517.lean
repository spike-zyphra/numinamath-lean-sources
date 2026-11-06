import Mathlib

theorem algebra_9106 (x : ℝ) : x ^ 2 - 4 * x + 3 < 0 ↔ 1 < x ∧ x < 3 := by 
  constructor
  · -- Assume x^2 - 4 x + 3 < 0, prove 1 < x ∧ x < 3
    intro h
    have h1 : x ^ 2 - 4 * x + 3 = (x - 1) * (x - 3) := by
      ring
    rw [h1] at h
    cases mul_neg_iff.mp h with
    | inl h2 =>
      constructor
      · linarith -- (x - 1) > 0 implies 1 < x
      · linarith -- (x - 3) < 0 implies x < 3
    | inr h2 =>
      -- impossible
      linarith -- impossible
  · -- Assume 1 < x ∧ x < 3, prove x^2 - 4 x + 3 < 0
    rintro ⟨h1, h2⟩
    have h3 : x ^ 2 - 4 * x + 3 = (x - 1) * (x - 3) := by
      ring
    rw [h3]
    have h4 : x - 1 > 0 := by linarith
    have h5 : x - 3 < 0 := by linarith
    exact mul_neg_of_pos_of_neg h4 h5