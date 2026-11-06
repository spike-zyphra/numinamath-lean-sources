import Mathlib

theorem algebra_189078 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h1 : 4 * x + 4 * y = 8) (h2 : x ^ 2 - y ^ 2 = 3) :
    x = 7 / 4 ∧ y = 1 / 4 := by
  have h3 : x + y = 2 := by
    linarith
  
  have h4 : x ^ 2 - y ^ 2 = (x + y) * (x - y) := by
    ring

  rw [h4] at h2
  rw [h3] at h2

  have h5 : x - y = 3 / 2 := by
    linarith

  have hx_eq : x = 7 / 4 := by
    linarith [h3, h5]

  have hy_eq : y = 1 / 4 := by
    linarith [h3, h5]

  constructor
  · exact hx_eq
  · exact hy_eq