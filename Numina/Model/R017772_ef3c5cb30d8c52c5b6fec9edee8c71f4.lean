import Mathlib

theorem algebra_1090 {x : ℝ} (hx : 4 * x ^ 4 + 3 * x ^ 3 - 2 * x ^ 2 + 3 * x + 4 = 0) :
    x + 1 / x = -2 ∨ x + 1 / x = 5 / 4 := by

  have h1 : x ≠ 0 := by
    by_contra h
    rw [h] at hx
    nlinarith
  
  have eq1 : 4 * (x ^ 2 + 1 / x ^ 2) + 3 * (x + 1 / x) - 2 = 0 := by
    have h3 : x ≠ 0 := h1
    have h4 : 4 * x ^ 4 + 3 * x ^ 3 - 2 * x ^ 2 + 3 * x + 4 = 0 := hx
    field_simp at *
    nlinarith [h4]

  have eq2 : 4 * (x + 1 / x) ^ 2 + 3 * (x + 1 / x) - 10 = 0 := by
    have h5 : x^2 + 1 / x^2 = (x + 1 / x)^2 - 2 := by
      field_simp
      ring
    nlinarith [eq1, h5]

  have h7 : (x + 1 / x - -2) * (x + 1 / x - 5 / 4) = 0 := by
    nlinarith [eq2]

  cases' (mul_eq_zero.mp h7) with h8 h9
  · left
    linarith

  · right
    linarith