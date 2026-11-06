import Mathlib

theorem algebra_183885 {x y : ℚ} (h : x - y ≠ 0) (h' : 1 / (x - y) = 3 / 4) (h'' : y = 5 / 18) :
    x = 29 / 18 := by
  have h1 : x - y = 4 / 3 := by
    field_simp [h] at h' ⊢
    linarith
  rw [h''] at h1
  linarith