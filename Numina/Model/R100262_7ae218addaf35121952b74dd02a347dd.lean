import Mathlib

theorem algebra_281291 {p : ℝ} (h : ∃ x1 x2, x1^2 + p * x1 + 2 * p = 0 ∧ x2^2 + p * x2 + 2 * p = 0 ∧ x1 = 3 * x2) :
    p = 0 ∨ p = 32 / 3 := by
  rcases h with ⟨x1, x2, h1, h2, h3⟩
  have eq1 : x1^2 + p * x1 + 2 * p = 0 := h1
  have eq2 : x2^2 + p * x2 + 2 * p = 0 := h2
  have eq3 : x1 = 3 * x2 := h3
  rw [eq3] at eq1
  have eq4 : (3 * x2)^2 + p * (3 * x2) + 2 * p = 0 := eq1
  have eq5 : 9 * x2^2 + 3 * p * x2 + 2 * p = 0 := by
    nlinarith
  have eq6 : x2 * (8 * x2 + 2 * p) = 0 := by
    nlinarith [eq2, eq5]
  cases (mul_eq_zero.mp eq6) with
  | inl h7 =>
    have hx2 : x2 = 0 := h7
    rw [hx2] at eq2
    have hp : p = 0 := by
      nlinarith
    left
    exact hp
  | inr h8 =>
    have h9 : x2 = -p / 4 := by
      linarith
    rw [h9] at eq2
    have : p * (32 - 3 * p) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp this) with
    | inl hp =>
      left
      exact hp
    | inr hp =>
      have hp2 : p = 32 / 3 := by
        linarith
      right
      exact hp2