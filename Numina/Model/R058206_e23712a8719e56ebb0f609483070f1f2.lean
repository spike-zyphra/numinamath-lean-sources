import Mathlib

theorem algebra_13711 {x y : ℝ}
    (hx : x = (2001 : ℝ)^1002 - 2001^(-1002 : ℤ))
    (hy : y = (2001 : ℝ)^1002 + 2001^(-1002 : ℤ)) :
    x^2 - y^2 = -4 := by
  rw [hx, hy]
  norm_num
  <;> ring_nf
  <;> norm_num