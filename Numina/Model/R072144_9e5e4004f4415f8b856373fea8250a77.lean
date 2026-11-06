import Mathlib

theorem algebra_118908 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (hxy : x = 5 * y) (h : 5 / x = 5 / y - 1) :
    5 / y = 1.25 := by
  have hx' : x ≠ 0 := by linarith
  have hy' : y ≠ 0 := by linarith

  rw [hxy] at h

  have eq1 : 5 / (5 * y) = 5 / y - 1 := by
    exact h

  have eq2 : 5 / (5 * y) = 1 / y := by
    field_simp [hy']
    <;> ring

  rw [eq2] at eq1

  have eq3 : y = 4 := by
    field_simp [hy'] at eq1 ⊢
    nlinarith

  rw [eq3]
  norm_num