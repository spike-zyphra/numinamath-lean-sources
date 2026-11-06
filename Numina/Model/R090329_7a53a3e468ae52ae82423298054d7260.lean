import Mathlib

theorem algebra_89124 {x : ℝ} (h : x^3 - x^2 = (x^2 - x)^2) :
    x = 0 ∨ x = 1 ∨ x = 2 := by
  have h1 : (x^2 - x)^2 = x^4 - 2*x^3 + x^2 := by ring
  rw [h1] at h
  have h2 : x^4 - 3*x^3 + 2*x^2 = 0 := by
    nlinarith
  have h3 : x^4 - 3*x^3 + 2*x^2 = x^2 * (x^2 - 3*x + 2) := by ring
  rw [h3] at h2
  have h4 : x^2 * (x^2 - 3*x + 2) = 0 := h2
  cases (mul_eq_zero.1 h4) with
  | inl h5 =>
    -- h5 is x^2 = 0, so x = 0
    left
    nlinarith
  | inr h6 =>
    -- h6 is x^2 - 3*x + 2 = 0
    have h7 : x^2 - 3*x + 2 = (x - 1) * (x - 2) := by ring
    rw [h7] at h6
    cases (mul_eq_zero.1 h6) with
    | inl h8 =>
      -- h8 is x - 1 = 0, so x = 1
      right
      left
      linarith
    | inr h9 =>
      -- h9 is x - 2 = 0, so x = 2
      right
      right
      linarith