import Mathlib

open Real

theorem algebra_8657 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
(h1 : a^2 + b + c = 1 / a) (h2 : b^2 + c + a = 1 / b) (h3 : c^2 + a + b = 1 / c) :
a = b ∨ b = c ∨ a = c := by
  have eq1 : a^3 + a * b + a * c = 1 := by
    have h1' : a^2 + b + c = 1 / a := h1
    have h4 : a * (a^2 + b + c) = 1 := by
      field_simp [ha] at h1' ⊢
      linarith
    calc
      a^3 + a * b + a * c = a * (a^2 + b + c) := by ring
      _ = 1 := by
        linarith [h4]

  have eq2 : b^3 + b * c + b * a = 1 := by
    have h2' : b^2 + c + a = 1 / b := h2
    have h4 : b * (b^2 + c + a) = 1 := by
      field_simp [hb] at h2' ⊢
      linarith
    calc
      b^3 + b * c + b * a = b * (b^2 + c + a) := by ring
      _ = 1 := by
        linarith [h4]

  have eq3 : c^3 + c * a + c * b = 1 := by
    have h3' : c^2 + a + b = 1 / c := h3
    have h4 : c * (c^2 + a + b) = 1 := by
      field_simp [hc] at h3' ⊢
      linarith
    calc
      c^3 + c * a + c * b = c * (c^2 + a + b) := by ring
      _ = 1 := by
        linarith [h4]

  have h4 : (a - b) * (a^2 + a * b + b^2 + c) = 0 := by
    nlinarith [eq1, eq2]

  have h5 : (b - c) * (b^2 + b * c + c^2 + a) = 0 := by
    nlinarith [eq2, eq3]

  have h6 : (c - a) * (c^2 + c * a + a^2 + b) = 0 := by
    nlinarith [eq3, eq1]

  cases (mul_eq_zero.1 h4) with
  | inl h4 =>
    left
    linarith
  | inr h4 =>
    cases (mul_eq_zero.1 h5) with
    | inl h5 =>
      right
      left
      linarith
    | inr h5 =>
      cases (mul_eq_zero.1 h6) with
      | inl h6 =>
        right
        right
        linarith
      | inr h6 =>
        nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]