import Mathlib

theorem algebra_166337 {x y : ℝ} (h1 : x^4 + x^2 * y^2 + y^4 = 91) (h2 : x^2 + x * y + y^2 = 13) :
    (x = 1 ∧ y = 3) ∨ (x = 3 ∧ y = 1) ∨ (x = -1 ∧ y = -3) ∨ (x = -3 ∧ y = -1) := by

  have h3 : x^2 + y^2 - x * y = 7 := by
    have eq1 : x^4 + x^2 * y^2 + y^4 = (x^2 + x * y + y^2) * (x^2 - x * y + y^2) := by
      ring_nf
    rw [show x^4 + x^2 * y^2 + y^4 = 91 by linarith [h1], show x^2 + x * y + y^2 = 13 by linarith [h2]] at eq1
    nlinarith

  have h4 : x^2 + y^2 = 10 := by
    nlinarith [h2, h3]

  have h5 : x * y = 3 := by
    nlinarith [h2, h3]

  have h6 : (x + y)^2 = 16 := by
    nlinarith [h4, h5]

  have h7 : (x - y)^2 = 4 := by
    nlinarith [h4, h5]

  have h8 : x + y = 4 ∨ x + y = -4 := by
    have h : (x + y) ^ 2 = 16 := h6
    have : (x + y) = 4 ∨ (x + y) = -4 := by
      have h1 : (x + y) ^ 2 - 16 = 0 := by linarith
      have h2 : ((x + y) - 4) * ((x + y) + 4) = 0 := by
        linarith [h1]
      cases (mul_eq_zero.mp h2) with
      | inl h3 =>
        left
        linarith
      | inr h3 =>
        right
        linarith
    exact this

  cases h8 with
  | inl h12 =>
    have h14 : x - y = 2 ∨ x - y = -2 := by
      have h : (x - y) ^ 2 = 4 := h7
      have : (x - y) = 2 ∨ (x - y) = -2 := by
        have h1 : (x - y) ^ 2 - 4 = 0 := by linarith
        have h2 : ((x - y) - 2) * ((x - y) + 2) = 0 := by
          linarith [h1]
        cases (mul_eq_zero.mp h2) with
        | inl h3 =>
          left
          linarith
        | inr h3 =>
          right
          linarith
      exact this

    cases h14 with
    | inl h16 =>
      have h9 : x = 3 := by
        nlinarith
      have h10 : y = 1 := by
        nlinarith
      simp [h9, h10]
      <;> tauto

    | inr h16 =>
      have h9 : x = 1 := by
        nlinarith
      have h10 : y = 3 := by
        nlinarith
      simp [h9, h10]
      <;> tauto

  | inr h12 =>
    have h14 : x - y = 2 ∨ x - y = -2 := by
      have h : (x - y) ^ 2 = 4 := h7
      have : (x - y) = 2 ∨ (x - y) = -2 := by
        have h1 : (x - y) ^ 2 - 4 = 0 := by linarith
        have h2 : ((x - y) - 2) * ((x - y) + 2) = 0 := by
          linarith [h1]
        cases (mul_eq_zero.mp h2) with
        | inl h3 =>
          left
          linarith
        | inr h3 =>
          right
          linarith
      exact this

    cases h14 with
    | inl h16 =>
      have h9 : x = -1 := by
        nlinarith
      have h10 : y = -3 := by
        nlinarith
      simp [h9, h10]
      <;> tauto

    | inr h16 =>
      have h9 : x = -3 := by
        nlinarith
      have h10 : y = -1 := by
        nlinarith
      simp [h9, h10]
      <;> tauto