import Mathlib

theorem inequalities_240474 (x : ℝ) (h : (x^2 < 1 ∧ (1 - x)^2 > 1) ∨ (x^2 > 1 ∧ (1 - x)^2 < 1)) :
    0 < x^2 - x ∧ x^2 - x < 2 := by
  rcases h with (h | h)
  -- First case: x^2 < 1 ∧ (1 - x)^2 > 1
  · have h1 : x ^ 2 < 1 := h.1
    have h2 : (1 - x) ^ 2 > 1 := h.2
    have h3 : x < 0 := by
      nlinarith [sq_nonneg (1 - x)]
    have h4 : -1 < x := by
      nlinarith [sq_nonneg x]
    have h5 : 0 < x^2 - x := by
      nlinarith
    have h6 : x^2 - x < 2 := by
      nlinarith
    constructor
    · exact h5
    · exact h6
  -- Second case: x^2 > 1 ∧ (1 - x)^2 < 1
  · have h1 : x ^ 2 > 1 := h.1
    have h2 : (1 - x) ^ 2 < 1 := h.2
    have h3 : 0 < x := by
      nlinarith [sq_nonneg (1 - x)]
    have h4 : 1 < x := by
      nlinarith [sq_nonneg (1 - x)]
    have h5 : x < 2 := by
      nlinarith
    have h6 : 0 < x^2 - x := by
      nlinarith
    have h7 : x^2 - x < 2 := by
      nlinarith
    constructor
    · exact h6
    · exact h7