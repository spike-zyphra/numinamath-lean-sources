import Mathlib

theorem algebra_99951 {p : ℝ} (hp : p > 0) (h : (1 + p / 100) * (1 - x / 100) = 1) :
    x = 100 * p / (100 + p) := by
  have h1 : 100 + p ≠ 0 := by
    linarith
  have eq1 : x = 100 * p / (100 + p) := by
    field_simp [(show 100 + p ≠ 0 by linarith)] at h ⊢
    <;> nlinarith [h]
  exact eq1