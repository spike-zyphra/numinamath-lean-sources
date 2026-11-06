import Mathlib

theorem algebra_287176 {a b c d : ℝ} (h : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0)
    (h_plus : c + d ≠ 0) (h_minus : c - d ≠ 0) (h1 : a / b = c / d) :
    a * b / (c * d) = ((a + b) / (c + d)) ^ 2 ∨ a * b / (c * d) = ((a - b) / (c - d)) ^ 2 := by
  have h2 : a * d = b * c := by
    have hb : b ≠ 0 := h.2.1
    have hd : d ≠ 0 := h.2.2.2
    field_simp [hb, hd] at h1 ⊢
    linarith
  have h37 : (a * b) * (c + d) ^ 2 = (a + b) ^ 2 * (c * d) ∨ (a * b) * (c - d) ^ 2 = (a - b) ^ 2 * (c * d) := by
    have h38 : (a * b) * (c + d) ^ 2 = (a + b) ^ 2 * (c * d) := by
      have eq1 : a * b * (c ^ 2 + d ^ 2) = (a ^ 2 + b ^ 2) * (c * d) := by
        have heq : a * d = b * c := h2
        nlinarith [sq_nonneg (a * d - b * c), sq_nonneg (a - c), sq_nonneg (b - d), sq_pos_of_ne_zero (show a ≠ 0 by tauto), sq_pos_of_ne_zero (show b ≠ 0 by tauto), sq_pos_of_ne_zero (show c ≠ 0 by tauto), sq_pos_of_ne_zero (show d ≠ 0 by tauto)]
      nlinarith
    apply Or.inl
    nlinarith
  cases h37 with
  | inl h37 =>
    have h5 : a * b / (c * d) = ((a + b) / (c + d)) ^ 2 := by
      have ha : a ≠ 0 := h.1
      have hb : b ≠ 0 := h.2.1
      have hc : c ≠ 0 := h.2.2.1
      have hd : d ≠ 0 := h.2.2.2
      have hc2 : c + d ≠ 0 := h_plus
      field_simp [hc, hd, hc2] at h37 ⊢
      nlinarith
    left
    exact h5
  | inr h37 =>
    have h6 : a * b / (c * d) = ((a - b) / (c - d)) ^ 2 := by
      have ha : a ≠ 0 := h.1
      have hb : b ≠ 0 := h.2.1
      have hc : c ≠ 0 := h.2.2.1
      have hd : d ≠ 0 := h.2.2.2
      have hc3 : c - d ≠ 0 := h_minus
      field_simp [hc, hd, hc3] at h37 ⊢
      nlinarith
    right
    exact h6