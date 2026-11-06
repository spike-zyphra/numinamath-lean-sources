import Mathlib

theorem algebra_197999 {a b : ℝ} (ha : a ≠ -b) (hb : a ≠ b) (h : 2*a/(a+b) + b/(a-b) = 2) :
    (3*a - b)/(a + 5*b) = 3 ∨ (3*a - b)/(a + 5*b) = 1 := by

  have h1 : a + b ≠ 0 := by
    by_contra h1
    have : a = -b := by linarith
    contradiction

  have h2 : a - b ≠ 0 := by
    by_contra h2
    have : a = b := by linarith
    contradiction

  have eq1 : 2 * a * (a - b) + b * (a + b) = 2 * (a + b) * (a - b) := by
    have h3 : (a + b) ≠ 0 := h1
    have h4 : (a - b) ≠ 0 := h2
    field_simp [h3, h4] at h ⊢
    linarith

  have eq2 : b * (3 * b - a) = 0 := by
    nlinarith

  cases (mul_eq_zero.mp eq2) with
  | inl hb0 =>
    have h3 : b = 0 := hb0
    have ha1 : a ≠ 0 := by
      by_contra h4
      have : a = 0 := by linarith
      have h5 : a = -b := by
        rw [h3]
        linarith
      contradiction
    have h5 : (3 * a - b) / (a + 5 * b) = 3 := by
      have h7 : b = 0 := h3
      rw [h7]
      have h8 : a ≠ 0 := ha1
      field_simp [h8]
      <;> nlinarith
    left
    linarith
  | inr h_eq =>
    have h6 : a = 3 * b := by
      linarith
    have h7 : b ≠ 0 := by
      by_contra h8
      have : a = 0 := by
        rw [h6]
        linarith [h8]
      have h8 : a = b := by
        rw [this]
        linarith [h8]
      contradiction
    have h8 : (3 * a - b) / (a + 5 * b) = 1 := by
      rw [show a = 3 * b by linarith]
      have h9 : b ≠ 0 := h7
      field_simp [show (3 * b : ℝ) + 5 * b ≠ 0 by
        by_contra h10
        have : b = 0 := by
          linarith
        contradiction
      ]
      <;> nlinarith
    right
    linarith