import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_278163 {f : ℝ → ℝ} (hf : f = λ x => logb (1/2) (-x^2 - 2*x + 3)) :
    StrictMonoOn f (Ico (-1) 1) := by
  rw [hf]
  intro x hx y hy hxy
  have h1 : -1 ≤ x := hx.1
  have h2 : x < 1 := hx.2
  have h3 : -1 ≤ y := hy.1
  have h4 : y < 1 := hy.2
  have h5 : -x^2 - 2*x + 3 > 0 := by
    nlinarith
  have h6 : -y^2 - 2*y + 3 > 0 := by
    nlinarith
  have h7 : -x^2 - 2*x + 3 > -y^2 - 2*y + 3 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + 1), sq_nonneg (y + 1)]
  have h9 : logb (1 / 2) (-x^2 - 2 * x + 3) < logb (1 / 2) (-y^2 - 2 * y + 3) := by
    apply Real.logb_lt_logb_of_base_lt_one
    all_goals nlinarith
    all_goals nlinarith
    all_goals nlinarith
  linarith