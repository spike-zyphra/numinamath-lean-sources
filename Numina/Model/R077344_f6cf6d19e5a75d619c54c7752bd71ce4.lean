import Mathlib

theorem algebra_197466 (x : ℝ) (hx : x ≠ 0 ∧ x ≠ 5) :
    (2 * x ^ 2 - 10 * x) / (x ^ 2 - 5 * x) = x - 3 ↔ False := by
  constructor
  · -- Assume left side is true, prove False
    intro h
    have h1 : x ≠ 0 := hx.1
    have h2 : x ≠ 5 := hx.2
    have eq1 : (2 * x ^ 2 - 10 * x) / (x ^ 2 - 5 * x) = 2 := by 
      have h3 : x ^ 2 - 5 * x ≠ 0 := by
        intro h4
        have : x = 0 ∨ x = 5 := by
          have h5 : x * (x - 5) = 0 := by linarith
          cases (mul_eq_zero.mp h5) with
          | inl h6 =>
            left
            linarith
          | inr h7 =>
            right
            linarith
        cases this with
        | inl h7 =>
          exfalso
          exact h1 (by linarith)
        | inr h8 =>
          exfalso
          exact h2 (by linarith)
      have h4 : (2 * x ^ 2 - 10 * x) = 2 * (x ^ 2 - 5 * x) := by
        ring
      field_simp [h3]
      <;> linarith [h4]
    have eq2 : x = 5 := by
      linarith [h, eq1]
    have h3 : x ≠ 5 := h2
    contradiction
  · -- Assume False, prove equation
    intro h
    cases h