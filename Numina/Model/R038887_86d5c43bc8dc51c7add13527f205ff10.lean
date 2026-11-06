import Mathlib

theorem algebra_116189 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x = 1 / y) :
    (x - 1 / x) * (y + 1 / y) = x ^ 2 - y ^ 2 := by
  have h1 : y = 1 / x := by
    field_simp [show y ≠ 0 by exact hy, hx] at *
    <;> nlinarith [hxy]
  have h2 : 1 / x = y := by 
    linarith [h1]
  have h4 : 1 / y = x := by 
    field_simp [show y ≠ 0 by exact hy, hx] at *
    <;> nlinarith [hxy]
  have h5 : x - 1 / x = x - y := by
    rw [show 1 / x = y by linarith [h2]]
  have h6 : y + 1 / y = y + x := by 
    rw [show 1 / y = x by linarith [h4]]
  calc
    (x - 1 / x) * (y + 1 / y) = (x - y) * (y + x) := by 
      rw [h5, h6]
    _ = (x - y) * (x + y) := by 
      ring
    _ = x^2 - y^2 := by
      ring