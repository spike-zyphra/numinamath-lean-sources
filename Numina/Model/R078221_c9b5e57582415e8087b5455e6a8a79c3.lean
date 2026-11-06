import Mathlib

theorem algebra_5119 (x : ℝ) (hx : x > 0) (h : 1 / x = 1 / 60 + 1 / 90) :
    x = 36 := by
  have h1 : x ≠ 0 := by linarith
  have eq1 : 1 / x = 1 / 36 := by
    rw [h]
    norm_num
  have eq2 : x = 36 := by
    field_simp [h1] at eq1 ⊢
    linarith
  exact eq2