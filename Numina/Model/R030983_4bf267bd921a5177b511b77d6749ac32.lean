import Mathlib

theorem inequalities_201200 (a b c d : ℝ) (h₀ : 0 < d) (h₁ : d < b) (h₂ : a / b < c / d) :
    (a + c) / (b + d) < (a / b + c / d) / 2 := by
  have h3 : 0 < b := by linarith
  have h4 : a * d < c * b := by
    have h5 : b > 0 := h3
    have h6 : d > 0 := h₀
    have h7 : a / b - c / d < 0 := by linarith
    have h8 : (a / b - c / d) = (a * d - c * b) / (b * d) := by
      field_simp
      <;> ring
    rw [h8] at h7
    apply (div_neg_iff).mp at h7
    cases h7 with
    | inl h8 =>
      nlinarith
    | inr h9 =>
      nlinarith
  -- We want to show that (a + c) / (b + d) - ( (a / b + c / d) / 2 ) < 0
  have h6 : (a + c) / (b + d) - ( (a / b + c / d) / 2 ) < 0 := by
    have h5' : 0 < (b + d) := by linarith
    have h7 : 0 < b := by linarith
    have h8 : 0 < d := by linarith
    have h6' : (a + c) / (b + d) - ( (a / b + c / d) / 2 ) =
        ( (2 * b * d * (a + c) - (b + d) * (a * d + b * c) ) / ( 2 * b * d * (b + d) ) ) := by
      field_simp
      <;> ring
    rw [h6']
    apply div_neg_of_neg_of_pos
    -- Show that the numerator is negative.
    have h7 : 2 * b * d * (a + c) - (b + d) * (a * d + b * c) = (b - d) * (a * d - b * c) := by
      ring_nf
    rw [h7]
    have h8 : a * d - b * c < 0 := by nlinarith
    have h9 : (b - d) * (a * d - b * c) < (0 : ℝ) := by
      apply mul_neg_of_pos_of_neg
      · -- Show that b - d > 0
        nlinarith
      · -- Show that a * d - b * c < 0
        linarith
    linarith
    -- Show that the denominator is positive.
    positivity
  linarith