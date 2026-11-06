import Mathlib

theorem inequalities_189167 (x : ℝ) : x^3 - 9 * x > 0 ↔ (-3 < x ∧ x < 0) ∨ (x > 3) := by
  constructor
  · -- Assume x^3 - 9 * x > 0, prove (-3 < x ∧ x < 0) ∨ (x > 3)
    intro h
    have h1 : x * (x^2 - 9) > 0 := by nlinarith
    cases (mul_pos_iff.mp h1) with
    | inl h2 =>
      -- Case x > 0 and x^2 - 9 > 0.
      have h3 : x > 0 := by linarith
      have h4 : x^2 - 9 > 0 := by linarith
      have h5 : x > 3 := by nlinarith
      right
      linarith
    | inr h2 =>
      -- Case x < 0 and x^2 - 9 < 0.
      have h3 : x < 0 := by linarith
      have h4 : x^2 - 9 < 0 := by linarith
      have h5 : -3 < x := by nlinarith
      left
      constructor
      · linarith
      · linarith
  · -- Assume (-3 < x ∧ x < 0) ∨ (x > 3), prove x^3 - 9 * x > 0
    rintro (h | h)
    · -- Case (-3 < x ∧ x < 0)
      have h1 : x < 0 := h.2
      have h2 : -3 < x := h.1
      have h3 : x ^ 2 - 9 < 0 := by nlinarith
      have h4 : x * (x^2 - 9) > 0 := by nlinarith
      nlinarith
    · -- Case (x > 3)
      have h1 : x > 3 := h
      have h4 : x ^ 2 - 9 > 0 := by nlinarith
      have h5 : x * (x^2 - 9) > 0 := by nlinarith
      nlinarith