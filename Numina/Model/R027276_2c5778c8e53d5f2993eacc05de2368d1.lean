import Mathlib

theorem algebra_165550 {x : ℝ} (hx : x ≠ 0 ∧ x ≠ -2) :
    1 / x ^ 2 + 1 / (x + 2) ^ 2 = 10 / 9 ↔ x = -3 ∨ x = 1 := by
  constructor
  · -- Assume the equation holds, prove $x = -3 ∨ x = 1$.
    intro h_eq
    have hx1 : x ≠ 0 := hx.1
    have hx2 : x ≠ -2 := hx.2
    have h1 : x + 2 ≠ 0 := by
      intro h
      apply hx2
      linarith
    have eq1 : 1 / x ^ 2 + 1 / (x + 2) ^ 2 = (x^2 + (x + 2)^2) / (x^2 * (x + 2)^2) := by
      field_simp [show x ≠ 0 by exact hx1, show x + 2 ≠ 0 by exact h1]
      <;> ring
    have eq2 : (x^2 + (x + 2)^2) / (x^2 * (x + 2)^2) = 10 / 9 := by
      linarith [h_eq, eq1]
    have eq3 : x^2 + (x + 2)^2 = 10 / 9 * (x^2 * (x + 2)^2) := by
      have h2 : x^2 * (x + 2) ^ 2 ≠ 0 := by
        apply mul_ne_zero
        · -- show x^2 ≠ 0
          exact pow_ne_zero 2 hx1
        · -- show (x + 2)^2 ≠ 0
          exact pow_ne_zero 2 h1
      field_simp [h2] at eq2 ⊢
      nlinarith
    have eq5 : 9 * (x ^ 2 + (x + 2) ^ 2) = 10 * (x ^ 2 * (x + 2) ^ 2) := by
      nlinarith [eq3]
    have eq6 : (x + 1) ^ 2 = 4 := by
      nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by exact hx1), sq_pos_of_ne_zero (show (x + 2) ≠ 0 by exact h1), sq_nonneg (x + 1), sq_nonneg (x^2 - 1), sq_nonneg ((x + 2)^2 - 1), sq_nonneg ((x + 1) ^ 2 - 4)]
    have eq7 : x + 1 = 2 ∨ x + 1 = -2 := by
      have h6 : (x + 1) ^ 2 - 4 = 0 := by nlinarith
      have h7 : (x + 1 - 2) * (x + 1 + 2) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h7) with
      | inl h8 =>
        left
        linarith
      | inr h9 =>
        right
        linarith
    cases eq7 with
    | inl h8 =>
      right
      linarith
    | inr h9 =>
      left
      linarith
  · -- Assume x = -3 ∨ x = 1, prove the equation.
    rintro (h | h)
    · -- x = -3
      rw [h]
      norm_num
    · -- x = 1
      rw [h]
      norm_num