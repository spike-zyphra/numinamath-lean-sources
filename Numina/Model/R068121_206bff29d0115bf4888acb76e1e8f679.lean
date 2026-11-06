import Mathlib

theorem algebra_208504 (a b c d : ℝ) (P : ℝ → ℝ)
    (hP : ∀ x, P x = x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d)
    (hP1 : P 1 = 2000) (hP2 : P 2 = 4000) (hP3 : P 3 = 6000) :
    P 9 + P (-5) = 12704 := by 
  have eq1 := hP 1
  rw [eq1] at hP1
  have eq2 := hP 2
  rw [eq2] at hP2
  have eq3 := hP 3
  rw [eq3] at hP3
  have eq9 := hP 9
  have eq5 := hP (-5)
  rw [eq9, eq5]
  linarith