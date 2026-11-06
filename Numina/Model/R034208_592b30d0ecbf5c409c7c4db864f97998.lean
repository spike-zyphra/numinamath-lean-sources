import Mathlib

theorem algebra_9194 (x : ℝ) : x^2 - x < 0 ↔ 0 < x ∧ x < 1 := by
  constructor
  · -- Assume x^2 - x < 0, prove 0 < x ∧ x < 1
    intro h
    have h1 : x * (x - 1) < 0 := by
      linarith
    cases mul_neg_iff.mp h1 with
    | inl h2 =>
      constructor
      · -- Show that 0 < x
        linarith [h2.1]
      · -- Show that x < 1
        linarith [h2.2]
    | inr h3 =>
      linarith
  · -- Assume 0 < x ∧ x < 1, prove x^2 - x < 0
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : x * (x - 1) < 0 := by
      have hx1 : 0 < x := h1
      have hx2 : x - 1 < 0 := by linarith
      exact mul_neg_of_pos_of_neg hx1 hx2
    linarith