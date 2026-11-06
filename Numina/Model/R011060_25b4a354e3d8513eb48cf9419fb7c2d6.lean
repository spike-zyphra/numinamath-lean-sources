import Mathlib

theorem algebra_8983 {a b : ℝ} (ha : a^2 + a - 3 = 0) (hb : b^2 + b - 3 = 0)(hab: a ≠ b) : a * b - 2023 * a - 2023 * b = 2020 := by 
  have h1 : a + b = -1 := by
    have h2 : a^2 + a - 3 = 0 := ha
    have h3 : b^2 + b - 3 = 0 := hb
    have h4 : a^2 + a - 3 - (b^2 + b - 3) = 0 := by linarith
    have h5 : (a - b) * (a + b + 1) = 0 := by
      ring_nf at h4 ⊢
      linarith
    cases (mul_eq_zero.mp h5) with
    | inl h6 =>
      exfalso
      apply hab
      linarith
    | inr h7 =>
      linarith
  have h2 : a * b = -3 := by
    have h3 : a + b = -1 := h1
    nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by
      intro h
      apply hab
      linarith 
    ), sq_nonneg (a - b), sq_nonneg (a + b + 1)]
  nlinarith [h1, h2]