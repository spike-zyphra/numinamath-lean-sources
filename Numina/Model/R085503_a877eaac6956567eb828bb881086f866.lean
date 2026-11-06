import Mathlib

theorem algebra_306080 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (hxy : x = 2 * y) (hxy' : x * 18 = y * 27) :
    x * 198 = y * 150 := by
  rw [hxy] at hxy'
  omega