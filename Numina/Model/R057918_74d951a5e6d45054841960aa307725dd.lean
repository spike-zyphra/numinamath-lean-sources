import Mathlib

theorem algebra_204217 (v1 v2 : ℝ) (h : v1 > 0) (h' : v2 > 0)
    (h1 : v2 = 1.5 * v1) (h2 : 6 / v1 = 32 / v2 + 2.24) :
    (32 - 6) / v2 = 28.8 := by
  rw [h1] at h2
  field_simp at h2 ⊢
  <;> nlinarith