import Mathlib

theorem algebra_8287
  {x y : ℝ}
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  (hxy : x - y = x * y) :
  1 / x - 1 / y = -1 := by
  have h1 : 1 / x - 1 / y = (y - x) / (x * y) := by
    field_simp [hx, hy]
    <;> ring
  have h2 : y - x = - (x - y) := by ring
  have h3 : y - x = - (x * y) := by
    rw [h2]
    rw [hxy]
  have h5 : (x * y) ≠ 0 := by
    apply mul_ne_zero
    exact hx
    exact hy
  have h4 : (y - x) / (x * y) = -1 := by
    rw [h3]
    field_simp [h5]
    <;> nlinarith [hxy, hx, hy]
  rw [h1]
  exact h4