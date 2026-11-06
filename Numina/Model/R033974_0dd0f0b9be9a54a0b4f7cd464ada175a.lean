import Mathlib

theorem algebra_213838 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (a b c : ℝ) (ha : a = x + 1 / x) (hb : b = y + 1 / y)
    (hc : c = x * y + 1 / (x * y)) :
    a^2 + b^2 + c^2 - a * b * c = 4 := by
  rw [ha, hb, hc]
  have h1 : x * (1 / x) = 1 := by
    field_simp [hx]
  have h2 : y * (1 / y) = 1 := by
    field_simp [hy]
  have h3 : (x * y) * (1 / (x * y)) = 1 := by
    field_simp [hx, hy]
  field_simp [hx, hy, show x * y ≠ 0 by
    apply mul_ne_zero
    exact hx
    exact hy]
  <;> ring