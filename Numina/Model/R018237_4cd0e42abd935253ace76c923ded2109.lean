import Mathlib

theorem algebra_243851 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a^2 + b + c = 1 / a) (h2 : b^2 + c + a = 1 / b) (h3 : c^2 + a + b = 1 / c) :
    a = b ∨ b = c ∨ a = c := by
  have eq1 : a^3 + a * b + a * c = 1 := by
    have h1' : a^2 + b + c = 1 / a := h1
    field_simp [ha] at h1' ⊢
    nlinarith [h1']
  have eq2 : b^3 + b * c + b * a = 1 := by
    have h2' : b^2 + c + a = 1 / b := h2
    field_simp [hb] at h2' ⊢
    nlinarith [h2']
  have eq3 : c^3 + c * a + c * b = 1 := by
    have h3' : c^2 + a + b = 1 / c := h3
    field_simp [hc] at h3' ⊢
    nlinarith [h3']
  have eq4 : (a - b) * (a^2 + a * b + b^2 + c) = 0 := by
    nlinarith [eq1, eq2]
  have eq5 : (b - c) * (b^2 + b * c + c^2 + a) = 0 := by
    nlinarith [eq2, eq3]
  cases (mul_eq_zero.mp eq4) with
  | inl h4 =>
    left
    linarith
  | inr h4 =>
    cases (mul_eq_zero.mp eq5) with
    | inl h5 =>
      right
      left
      linarith
    | inr h5 =>
      -- At this point, we have:
      -- h4 : a^2 + a * b + b^2 + c = 0
      -- h5 : b^2 + b * c + c^2 + a = 0
      -- ⊢ a = b ∨ b = c ∨ a = c
      have eq6 : (a - c) * (a + b + c - 1) = 0 := by
        nlinarith [h4, h5]
      cases (mul_eq_zero.mp eq6) with
      | inl h6 =>
        right
        right
        linarith
      | inr h7 =>
        have eq7 : a + b + c = 1 := by
          linarith
        have eq8 : a^2 + a * b + b^2 - a - b + 1 = 0 := by 
          have eq9 : c = 1 - a - b := by 
            linarith
          rw [eq9] at h4
          nlinarith
        have eq9 : a ^ 2 + b ^ 2 + a * b - a - b + 1 = 0 := by
          nlinarith [eq8]
        nlinarith [sq_nonneg (a + b - 1), sq_nonneg (b - 1/3), sq_nonneg (a - 1/3), sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_nonneg (a * b), sq_nonneg ((a + b) * c)]