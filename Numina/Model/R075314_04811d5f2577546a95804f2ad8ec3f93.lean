import Mathlib

theorem algebra_177577 (x : ℝ) (hx : x ≠ 2 / 7) :
    (8 - 3 * x) / (7 * x - 2) < 0 ↔ x ∈ Set.Iio (2 / 7) ∪ Set.Ioi (8 / 3) := by
  have h1 : (8 - 3 * x) / (7 * x - 2) < 0 ↔ ((8 - 3 * x) > 0 ∧ (7 * x - 2) < 0) ∨ ((8 - 3 * x) < 0 ∧ (7 * x - 2) > 0) := by
    apply div_neg_iff
    all_goals linarith
  rw [h1]
  constructor
  · -- Forward direction: fraction is negative implies x is in the union
    rintro (h | h)
    · -- Case where numerator > 0 and denominator < 0
      have h2 : x < 2 / 7 := by
        linarith
      left
      exact h2
    · -- Case where numerator < 0 and denominator > 0
      have h4 : x > 8 / 3 := by
        linarith
      right
      exact h4
  · -- Backward direction: x is in the union implies fraction is negative
    rintro (h | h)
    · -- Case where x < 2/7
      have h2 : x < 2 / 7 := h
      have h3 : (8 - 3 * x) > 0 := by
        linarith
      have h4 : (7 * x - 2) < 0 := by
        linarith
      left
      exact ⟨h3, h4⟩
    · -- Case where x > 8/3
      have h4 : x > 8 / 3 := h
      have h5 : (8 - 3 * x) < 0 := by
        linarith
      have h6 : (7 * x - 2) > 0 := by
        linarith
      right
      exact ⟨h5, h6⟩