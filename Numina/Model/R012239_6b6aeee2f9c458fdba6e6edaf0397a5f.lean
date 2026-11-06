import Mathlib
open Real

theorem algebra_95549 {a : ℝ} (ha : a ≠ 0) (h : (a + 1 / a) ^ 2 = 3) : a ^ 3 + 1 / a ^ 3 = 0 := by
  have h1 : a ^ 2 + 1 / a ^ 2 = 1 := by
    have h2 : (a + 1 / a) ^ 2 = a ^ 2 + 2 + 1 / a ^ 2 := by
      field_simp
      ring
    rw [h2] at h
    linarith
  have h2 : a ^ 2 + 1 / a ^ 2 = 1 := h1
  have h3 : a ^ 3 + 1 / a ^ 3 = (a + 1 / a) * (a ^ 2 - 1 + 1 / a ^ 2) := by
    field_simp
    ring
  have h4 : a ^ 2 + 1 / a ^ 2 - 1 = 0 := by
    linarith [h2]
  have h5 : a ^ 2 - 1 + 1 / a ^ 2 = 0 := by
    linarith [h4]
  rw [h5] at h3
  linarith