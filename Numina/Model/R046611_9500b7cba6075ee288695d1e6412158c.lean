import Mathlib.Tactic

theorem inequalities_133559
    (x y : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hxy : x + y = 2) :
    x^2 * y^2 * (x^2 + y^2) ≤ 2 := by
  have h1 : y = 2 - x := by linarith
  rw [h1]
  nlinarith [sq_nonneg (x - 1), sq_nonneg (x * (x - 1)), sq_nonneg ((2 - x) * (x - 1)), sq_nonneg (x * (2 - x) - 1), sq_nonneg (x ^ 2 - (2 - x) ^ 2), sq_nonneg (x * (2 - x)), sq_nonneg ((x - 1) * (x * (2 - x) - 1)), mul_pos hx (show 0 < 2 - x by nlinarith [hxy, hx, hy]), sq_nonneg ((x ^ 2 + (2 - x) ^ 2) - 2)]