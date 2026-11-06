import Mathlib

theorem algebra_10835 {a : ℝ} (ha : 4 = a + 1 / a) :
    a ^ 4 + 1 / a ^ 4 = 194 := by
  have ane0 : a ≠ 0 := by
    by_contra!
    simp [this] at ha
  have h1 : a ^ 2 + 1 / a ^ 2 = 14 := by
    field_simp [ane0] at *
    nlinarith
  field_simp [ane0] at *
  nlinarith [h1]