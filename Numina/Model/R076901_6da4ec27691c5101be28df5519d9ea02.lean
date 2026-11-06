import Mathlib

theorem algebra_286144 (a : ℝ) (ha : 0 < a) (h : 2 / 5 / a = 18 / 60) :
    1 / a = 45 / 60 := by
  have h1 : a = (2 / 5) / (18 / 60) := by
    field_simp at h ⊢
    nlinarith
  rw [h1]
  field_simp
  <;> norm_num