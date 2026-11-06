import Mathlib

theorem algebra_17217 {a b c : ℤ} (h₀ : ∀ x, x^2 + 13 * x + 30 = (x + a) * (x + b)) (h₁ : ∀ x, x^2 + 5 * x - 50 = (x + b) * (x - c)) : a + b + c = 18 := by
  have h0_eq1 := h₀ 0
  have h0_eq2 := h₀ 1
  have h0_eq3 := h₀ (-1)
  have h1_eq1 := h₁ 0
  have h1_eq2 := h₁ 1
  have h1_eq3 := h₁ (-1)
  have hab : a * b = 30 := by
    nlinarith
  have hbc : b * c = 50 := by
    nlinarith
  have h0_sum : a + b = 13 := by
    nlinarith
  have h1_sum : b - c = 5 := by
    nlinarith
  have ha1 : a = 3 ∨ a = 10 := by
    have hb_eq : b = 13 - a := by linarith  -- Using h0_sum: a + b = 13
    rw [hb_eq] at hab
    have h3 : a * (13 - a) = 30 := by linarith
    have h4 : a^2 - 13 * a + 30 = 0 := by
      ring_nf at h3
      linarith
    have h8 : (a - 3) * (a - 10) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h8) with ha3 ha10
    · -- Case a - 3 = 0
      left
      linarith
    · -- Case a - 10 = 0
      right
      linarith
  cases ha1 with
  | inl ha3 =>
    have hb10 : b = 10 := by
      linarith [h0_sum, ha3]
    have hc5 : c = 5 := by
      nlinarith [h1_sum, hb10]
    linarith [ha3, hb10, hc5]
  | inr ha10 =>
    have hb3 : b = 3 := by
      linarith [h0_sum, ha10]
    have hc2 : c = -2 := by
      nlinarith [h1_sum, hb3]
    have h7 : b * c = 50 := hbc
    rw [hb3, hc2] at h7
    nlinarith