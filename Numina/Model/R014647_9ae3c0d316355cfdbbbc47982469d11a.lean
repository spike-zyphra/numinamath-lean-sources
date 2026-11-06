import Mathlib

theorem algebra_204378 {a b c d : ℝ} (h₀ : 0 < d) (h₁ : d < b) (h₂ : a / b < c / d) :
    (a + c) / (b + d) < (a / b + c / d) / 2 := by
  have hb : 0 < b := by
    linarith
  have hb_pos : 0 < b := by
    linarith
  have h1 : 0 < b + d := by
    linarith
  have h3 : a / b < c / d := h₂
  have h4 : a * d < c * b := by
    have h4' : a / b < c / d := h₂
    have hb' : 0 < b := hb
    have hd' : 0 < d := h₀
    have h : a * d < c * b := by
      have h5 : a / b < c / d := h4'
      have h5' : a / b - c / d < 0 := by linarith
      have h7 : a / b - c / d = (a * d - c * b) / (b * d) := by
        field_simp
        <;> ring
      rw [h7] at h5'
      apply div_neg_iff.mp at h5'
      cases h5' with
      | inl h1 =>
        nlinarith
      | inr h2 =>
        nlinarith
    linarith
  have h5 : 2 * b * d * (a + c) < (b + d) * (a * d + b * c) := by
    have h4 : a * d < c * b := h4
    nlinarith [sq_nonneg (a * d - c * b), sq_nonneg (b - d), sq_nonneg (a), sq_nonneg (c), mul_pos h₀ (show 0 < b by linarith), mul_pos (show 0 < b by linarith) (show 0 < d by linarith), sq_pos_of_pos h₀, sq_pos_of_pos (show 0 < b by linarith), mul_pos (show 0 < d by linarith) (show 0 < b by linarith)]
  have h6 : (a + c) / (b + d) < (a / b + c / d) / 2 := by
    have h7 : (a + c) / (b + d) - ( (a / b + c / d) / 2 ) < 0 := by
      have h8 : ((a + c) / (b + d) - ( (a / b + c / d) / 2 )) = (2 * b * d * (a + c) - (b + d) * (a * d + b * c)) / (2 * b * d * (b + d)) := by
        field_simp
        ring
      rw [h8] at *
      apply div_neg_of_neg_of_pos
      · -- First part: Show the numerator is negative
        linarith [h5]
      · -- Second part: Show denominator is positive
        positivity
    linarith
  exact h6