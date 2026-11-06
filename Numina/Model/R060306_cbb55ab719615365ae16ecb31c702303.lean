import Mathlib

theorem algebra_14849 {x1 x2 y1 y2 : ℝ} (h : y1 = 13 ∧ y2 = 13) (h' : x1 ≠ x2) :
    (y2 - y1) / (x2 - x1) + y1 = 13 := by
  rcases h with ⟨hy1, hy2⟩
  rw [hy1, hy2]
  norm_num
  <;> intro h12
  <;> apply h'
  <;> linarith