import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_151573 {f : ℝ → ℝ} (hf : f = λ x => logb (1/2) (x^2 - 2*x - 3)) :
    StrictMonoOn f {x | x < -1} := by 
  intro x hx y hy hxy
  have hx1 : x < -1 := hx
  have hy1 : y < -1 := hy
  have hxy1 : x < y := hxy
  have hx2 : x ^ 2 - 2 * x - 3 > 0 := by nlinarith
  have hy2 : y ^ 2 - 2 * y - 3 > 0 := by nlinarith
  have h1 : x ^ 2 - 2 * x - 3 > y ^ 2 - 2 * y - 3 := by nlinarith [hxy1, hx1, hy1]
  rw [hf]
  have h2 : logb (1 / 2) (x ^ 2 - 2 * x - 3) < logb (1 / 2) (y ^ 2 - 2 * y - 3) := by
    apply Real.logb_lt_logb_of_base_lt_one
    all_goals
      nlinarith
  simpa using h2