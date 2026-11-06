import Mathlib

theorem algebra_180074 (x : ℝ) (hx : x ≠ 5 / 2) :
    (x + 3) * (5 - x) / (2 * x - 5) > 0 ↔ x < -3 ∨ x ∈ Set.Ioo 2.5 5 := by
  have h1 : 2 * x - 5 ≠ 0 := by
    intro h
    apply hx
    linarith
  constructor
  · -- Assume (x + 3) * (5 - x) / (2 * x - 5) > 0, prove x < -3 ∨ x ∈ Set.Ioo 2.5 5
    intro h
    have h2 : (x + 3) * (5 - x) / (2 * x - 5) > 0 := by
      simpa using h
    apply div_pos_iff.mp at h2
    cases h2 with
    | inl h3 =>
      -- Case where both numerator and denominator are positive
      have h3a : -3 < x := by
        nlinarith
      have h3b : 2.5 < x := by
        nlinarith
      have h3c : x < 5 := by
        nlinarith
      right
      exact ⟨by linarith, by linarith⟩
    | inr h3 =>
      -- Case where both numerator and denominator are negative
      have h3a : (x + 3) * (5 - x) < 0 := h3.1
      have h3b : 2 * x - 5 < 0 := h3.2
      have h3c : x < -3 := by
        nlinarith [sq_nonneg (x + 3), sq_nonneg (x - 5), sq_nonneg (2 * x - 5)]
      left
      linarith
  · -- Assume x < -3 ∨ x ∈ Set.Ioo 2.5 5, prove (x + 3) * (5 - x) / (2 * x - 5) > 0
    rintro (h | h)
    · -- Case x < -3
      have h1a : (x + 3) * (5 - x) < 0 := by
        nlinarith
      have h1b : 2 * x - 5 < 0 := by
        linarith
      have h4 : (x + 3) * (5 - x) / (2 * x - 5) > 0 := by
        apply div_pos_of_neg_of_neg
        all_goals nlinarith
      linarith
    · -- Case x ∈ Set.Ioo 2.5 5
      rcases h with ⟨h1a, h1b⟩
      have h2 : (x + 3) * (5 - x) > 0 := by
        nlinarith
      have h3 : 2 * x - 5 > 0 := by
        nlinarith
      have h4 : (x + 3) * (5 - x) / (2 * x - 5) > 0 := by
        apply div_pos
        all_goals nlinarith
      linarith