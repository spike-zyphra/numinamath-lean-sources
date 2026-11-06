import Mathlib

theorem algebra_245997 {a b c : ℝ} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (h : a / (b - c) + b / (c - a) + c / (a - b) = 0) :
    a / (b - c) ^ 2 + b / (c - a) ^ 2 + c / (a - b) ^ 2 = 0 := by
  have h1 : a / (b - c) + b / (c - a) + c / (a - b) = 0 := h
  have h5 : b - c ≠ 0 := by
    intro h5
    apply hb
    linarith
  have h6 : c - a ≠ 0 := by
    intro h6
    apply hc
    linarith
  have h7 : a - b ≠ 0 := by
    intro h7
    apply ha
    linarith
  have eq1 : a * (c - a) * (a - b) + b * (b - c) * (a - b) + c * (b - c) * (c - a) = 0 := by
    have h1' : a / (b - c) + b / (c - a) + c / (a - b) = 0 := h
    have h5 : b - c ≠ 0 := by
      intro h5
      apply hb
      linarith
    have h6 : c - a ≠ 0 := by
      intro h6
      apply hc
      linarith
    have h7 : a - b ≠ 0 := by
      intro h7
      apply ha
      linarith
    field_simp [h5, h6, h7] at h1' ⊢
    nlinarith
  field_simp [h5, h6, h7] at *
  nlinarith [sq_nonneg (a * (c - a) + b * (b - c) + c * (a - b)), sq_nonneg (a * (a - b) + b * (b - c) + c * (a - b)), sq_nonneg (a * (c - a) + b * (b - c) + c * (c - a)), sq_nonneg ( (c - a) * (a - b) + (b - c) * (b - c) + (b - c) * (c - a) ), sq_nonneg ( (b - c) * (a - b) - (c - a) * (b - c) ) ]