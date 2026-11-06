import Mathlib

theorem algebra_251311 (d : ℝ) (h : d > 0) (h1 : (d - 1) / (2 * d) = 1 / d) :
    d = 3 := by

  have h2 : d ≠ 0 := by linarith
  have h3 : (d - 1) / (2 * d) = 1 / d := h1
  have h4 : (d - 1) / 2 = 1 := by
    have h5 : (d - 1) / (2 * d) = 1 / d := h3
    have h6 : d ≠ 0 := h2
    have h7 : 2 * d ≠ 0 := by
      intro h8
      apply h6
      linarith
    have h8 : (d - 1) / (2 * d) * d = (1 / d) * d := by
      rw [h5]
    have h9 : (d - 1) / (2 * d) * d = (d - 1) / 2 := by
      field_simp [h6, h7]
      <;> ring
    have h10 : (1 / d) * d = 1 := by
      field_simp [h6]
    rw [h9, h10] at h8
    linarith

  linarith