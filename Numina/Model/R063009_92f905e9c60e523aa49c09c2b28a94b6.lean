import Mathlib

theorem algebra_84856 (a b c : ℝ) (ha : a^3 - 2 * a^2 + 3 * a - 4 = 0) (hb : b^3 - 2 * b^2 + 3 * b - 4 = 0) (hc : c^3 - 2 * c^2 + 3 * c - 4 = 0) (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    1 / (a * (b^2 + c^2 - a^2)) + 1 / (b * (c^2 + a^2 - b^2)) + 1 / (c * (a^2 + b^2 - c^2)) = -1 / 8 := by
  have h2 : a = b := by
    have h3 : a^3 - 2 * a^2 + 3 * a - 4 = 0 := ha
    have h4 : b^3 - 2 * b^2 + 3 * b - 4 = 0 := hb
    have h5 : a^3 - 2 * a^2 + 3 * a - 4 - (b^3 - 2 * b^2 + 3 * b - 4) = 0 := by
      linarith
    have h6 : (a - b) * (a^2 + a * b + b^2 - 2 * (a + b) + 3) = 0 := by
      ring_nf at h5 ⊢
      linarith
    cases (mul_eq_zero.mp h6) with
    | inl h7 =>
      have h8 : a - b = 0 := by linarith
      linarith
    | inr h8 =>
      have h7 : (a - b)^2 + (a + b - 2)^2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2)]
      have h8 : (a - b)^2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2)]
      have h9 : a - b = 0 := by
        nlinarith
      linarith
  have h14 : a = b := h2
  have h15 : a ≠ b := hdist.1
  contradiction