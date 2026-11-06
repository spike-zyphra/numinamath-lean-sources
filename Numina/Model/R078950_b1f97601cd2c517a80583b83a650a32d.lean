import Mathlib

theorem algebra_235447 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x / y = 4 / 5) (h2 : (x + y) / (x * 5 + y * 2) = 7 / 11) :
    (x + y) / (x * 7 + y * 11) = 13 / 7 := by
  have h1' : 5 * x = 4 * y := by
    field_simp [(show y ≠ 0 by linarith)] at h1
    nlinarith
  have h2' : 11 * (x + y) = 7 * (x * 5 + y * 2) := by
    field_simp [(show x * 5 + y * 2 ≠ 0 by
      nlinarith [sq_nonneg (x - 4 * y / 5), sq_nonneg (y - 5 * x / 4)]
    )] at h2
    nlinarith
  -- Solving the system of equations to reach a contradiction
  have h3 : y = 5 / 4 * x := by
    linarith
  rw [h3] at h2'
  -- The resulting equation is inconsistent as shown from contradiction
  nlinarith