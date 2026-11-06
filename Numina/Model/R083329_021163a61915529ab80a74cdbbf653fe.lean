import Mathlib

theorem algebra_20798 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a * b = a - b) :
    {x | x = a / b + b / a - a * b} = {2} := by
  have h1 : a / b + b / a - a * b = 2 := by
    field_simp [ha, hb] at h ⊢
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a - b)]
  ext x
  simp [h1]
  <;> tauto