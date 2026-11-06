import Mathlib

theorem algebra_164572 (x : ℝ) (hx : x ≠ 0) (h : 1050 - 840 / x * 8 = 90) : x = 7 := by
  field_simp at h ⊢
  <;> nlinarith [show x ≠ 0 by exact hx]