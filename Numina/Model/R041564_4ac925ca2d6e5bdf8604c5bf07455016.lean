import Mathlib

theorem algebra_95028 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : y - 1 / x ≠ 0) :
    (x - 1 / y) / (y - 1 / x) = x / y := by
  have eq1 : x - 1 / y = (x * y - 1) / y := by
    field_simp [hy]
    <;> ring
  have eq2 : y - 1 / x = (x * y - 1) / x := by
    field_simp [hx]
    <;> ring
  have h2 : x * y - 1 ≠ 0 := by
    by_contra h
    have h3 : y - 1 / x = 0 := by 
      rw [eq2]
      rw [h]
      norm_num
    contradiction
  rw [eq1, eq2]
  field_simp [h2, hx, hy]
  <;> ring