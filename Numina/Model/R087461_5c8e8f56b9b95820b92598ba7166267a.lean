import Mathlib

open Real

theorem algebra_313123 {x y : ℝ} (hx : x ≥ 0) (hy : y ≥ 0)
    (h : x + y = 3) (p q : ℝ) (hp : p = (1 / 5) * x) (hq : q = (3 / 5) * sqrt y) :
    p + q ≤ 1.05 := by
  have h1 : y = 3 - x := by linarith
  rw [h1] at hq
  have h3 : 3 - x ≥ 0 := by linarith
  rw [hp, hq]
  have h4 : Real.sqrt (3 - x) ≥ 0 := Real.sqrt_nonneg (3 - x)
  have h5 : (Real.sqrt (3 - x)) ^ 2 = 3 - x := Real.sq_sqrt (show 3 - x ≥ 0 by linarith)
  nlinarith [sq_nonneg (Real.sqrt (3 - x) - 3 / 2), sq_nonneg (x - 3 / 4),
          Real.sqrt_nonneg (3 - x),
          Real.sq_sqrt (show (3 - x) ≥ 0 by linarith),
          sq_nonneg ((Real.sqrt (3 - x) ) - 3 / 2),
          sq_nonneg (x - 3 / 4)]