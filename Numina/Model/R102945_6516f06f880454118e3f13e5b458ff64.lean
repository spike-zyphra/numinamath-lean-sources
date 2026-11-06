import Mathlib

theorem algebra_242421 (x : ℝ) (hx : x ≠ 0) (h : (1.5 * x) * 2.5 = 3.5) :
    (100 * x) * 45 = 4200 := by
  have hx_eq : x = 3.5 / (1.5 * 2.5 : ℝ) := by
    field_simp at h ⊢
    linarith
  rw [hx_eq]
  norm_num