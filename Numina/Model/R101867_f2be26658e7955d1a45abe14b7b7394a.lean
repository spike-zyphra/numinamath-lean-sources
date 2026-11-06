import Mathlib

theorem algebra_10656 {a b c : ℝ} (ha : a ≠ 0) (h : ∀ x y, x = a * y ^ 2 + b * y + c ↔ x = -(y + 4) ^ 2 / 2 + 5) :
    a + b + c = -15 / 2 := by
  have h1 := h (-15 / 2) 1
  norm_num at h1
  linarith