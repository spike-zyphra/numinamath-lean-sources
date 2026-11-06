import Mathlib

theorem algebra_195549 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x = 250 / 100 * y) (hc : 2 * y = c / 100 * x) :
    c = 80 := by
  have eq1 : 2 * y = c / 100 * x := hc
  rw [show x = 250 / 100 * y by linarith] at eq1
  have eq2 : 2 * y = c / 40 * y := by
    linarith
  have h3 : 2 = c / 40 := by
    apply (mul_left_inj' hy).mp
    linarith
  linarith