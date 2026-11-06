import Mathlib

theorem algebra_145953 (p m : ℝ) (hp : p > 0) (hm : m > 0)
    (h1 : p = m - 2) (h2 : m = (p + 2) / (1 + 2 / p)) :
    p = 12 := by
  have h3 : p ≠ 0 := by linarith
  have h4 : 1 + 2 / p = (p + 2) / p := by
    field_simp [h3]
    <;> linarith
  have h5 : m = p := by
    rw [h4] at h2
    field_simp [(show p + 2 ≠ 0 by nlinarith), h3] at h2 ⊢
    <;> linarith [h2]
  linarith [h1, h5]