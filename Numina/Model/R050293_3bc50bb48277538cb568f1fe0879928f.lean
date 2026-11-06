import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_134517 {f : ℝ → ℝ} (hf : f = λ x => logb (1/2) (x^2 - 2*x - 3)) :
    StrictMonoOn f (Iio (-1)) := by 
  intro x hx y hy hxy
  have h1 : x < -1 := by 
    simpa using hx
  have h2 : y < -1 := by 
    simpa using hy
  have h3 : x ^ 2 - 2 * x - 3 > 0 := by nlinarith 
  have h4 : y ^ 2 - 2 * y - 3 > 0 := by nlinarith
  have h5 : x ^ 2 - 2 * x - 3 > y ^ 2 - 2 * y - 3 := by nlinarith [sq_nonneg (x - y), sq_nonneg (x + 1), sq_nonneg (y + 1)]
  rw [hf]
  have h6 : logb (1 / 2) (x ^ 2 - 2 * x - 3) < logb (1 / 2) (y ^ 2 - 2 * y - 3) := by 
    apply logb_lt_logb_of_base_lt_one 
    all_goals nlinarith 
    all_goals nlinarith 
  apply h6 
  all_goals nlinarith