import Mathlib

open Real

theorem algebra_2916 {x : ℝ} {n : ℤ} :
  (cosh x + sinh x) ^ n = cosh (n * x) + sinh (n * x) := by 
  have h1 : cosh x + sinh x = exp x := by 
    rw [Real.cosh_eq, Real.sinh_eq]
    ring 
  rw [h1]
  have h2 : (exp x) ^ n = exp (n * x) := by 
    simp [Real.exp_mul, zpow_natCast, mul_comm]
  rw [h2]
  have h3 : exp (n * x) = cosh (n * x) + sinh (n * x) := by 
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  rw [h3]