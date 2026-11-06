import Mathlib

theorem algebra_14752 {a : ℝ} (ha : ∃ b c, ∀ x, a*x^2 + 12*x + 9 = (b + c*x)^2) :
    a = 4 := by
  rcases ha with ⟨b, c, h⟩
  have eq0 := h 0
  have eq1 := h 1
  have eq2 := h (-1)
  have h1 : b ^ 2 = 9 := by
    nlinarith
  have h2 : a + 21 = (b + c) ^ 2 := by
    nlinarith
  have h3 : a - 3 = (b - c) ^ 2 := by
    nlinarith
  have h4 : b = 3 ∨ b = -3 := by
    have h5 : b ^ 2 - 9 = 0 := by linarith
    have h6 : (b - 3) * (b + 3) = 0 := by
      nlinarith
    cases (mul_eq_zero.1 h6) with
    | inl h7 =>
      left
      linarith
    | inr h8 =>
      right
      nlinarith
  cases h4 with
  | inl hbl =>
    have eq2 := h2
    rw [hbl] at eq2
    have eq3 := h3
    rw [hbl] at eq3
    nlinarith
  | inr hb2 =>
    have eq2 := h2
    rw [hb2] at eq2
    have eq3 := h3
    rw [hb2] at eq3
    nlinarith