import Mathlib

theorem algebra_196109 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x = 250 / 100 * y) (h2y : 2 * y = c / 100 * x) :
    c = 80 := by
  rw [show x = 250 / 100 * y by linarith] at h2y
  have eq2 : 2 * y = (250 * c / 10000) * y := by
    nlinarith
  have h4 : 2 * y = (c / 40) * y := by
    nlinarith [eq2]
  have h5 : 2 - c / 40 = 0 := by
    apply (mul_left_inj' hy).mp
    linarith [h4]
  linarith