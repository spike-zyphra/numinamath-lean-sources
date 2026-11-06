import Mathlib

theorem algebra_155022 {a b c : ℝ} (h₀ : a + b + c = 0) (h₁ : a * b * c < 0) :
    (a ^ 2 + b ^ 2) / c + (b ^ 2 + c ^ 2) / a + (c ^ 2 + a ^ 2) / b > 0 := by
  have h₂ : a ≠ 0 := by
    by_contra h
    rw [h] at h₁
    nlinarith
  have h₃ : b ≠ 0 := by
    by_contra h
    rw [h] at h₁
    nlinarith
  have h₄ : c ≠ 0 := by
    by_contra h
    rw [h] at h₁
    nlinarith
  have h5 : (a ^ 2 + b ^ 2) / c + (b ^ 2 + c ^ 2) / a + (c ^ 2 + a ^ 2) / b =
      (a^3 * b + a * b^3 + b^3 * c + b * c^3 + c^3 * a + c * a^3) / (a * b * c) := by
    field_simp [h₂, h₃, h₄]
    ring
  rw [h5]
  have h6 : a * b * c < 0 := h₁
  have h7 : a^3 * b + a * b^3 + b^3 * c + b * c^3 + c^3 * a + c * a^3 < 0 := by
    have h8 : a + b + c = 0 := h₀
    have h9 : c = -(a + b) := by linarith
    rw [h9]
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a * b), sq_nonneg (a * (a + b)), sq_nonneg (b * (a + b)), sq_nonneg (a * b * (a + b)), sq_nonneg (a * b * (a - b)), sq_nonneg (a * b * (-(a + b)) ) ]
  apply div_pos_of_neg_of_neg h7 (by nlinarith)