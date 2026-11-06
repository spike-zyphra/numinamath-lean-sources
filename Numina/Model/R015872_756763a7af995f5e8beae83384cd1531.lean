import Mathlib

theorem algebra_242197 {a b c : ℝ} (h : a * b * c = 1) :
    (a + 1 / a) * (b + 1 / b) * (c + 1 / c) =
    (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 + (c + 1 / c) ^ 2 - 4 := by

  have ha1 : 1 / a = b * c := by
    have h1 : a * b * c = 1 := h
    have ha2 : a ≠ 0 := by
      by_contra h'
      have : a * b * c = 0 := by
        rw [h']
        norm_num
      linarith
    field_simp [ha2]
    nlinarith

  have hb1 : 1 / b = a * c := by
    have h1 : a * b * c = 1 := h
    have hb2 : b ≠ 0 := by
      by_contra h'
      have : a * b * c = 0 := by
        rw [show b = 0 by linarith]
        norm_num
      linarith
    field_simp [hb2]
    nlinarith

  have hc1 : 1 / c = a * b := by
    have h1 : a * b * c = 1 := h
    have hc2 : c ≠ 0 := by
      by_contra h'
      have : a * b * c = 0 := by
        rw [show c = 0 by linarith]
        norm_num
      linarith
    field_simp [hc2]
    nlinarith

  rw [ha1, hb1, hc1]
  ring_nf
  <;> nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
      sq_nonneg (a * c - 1), sq_nonneg (b * a - 1), sq_nonneg (c * b - 1),
      sq_nonneg (a * b * c - 1), h]