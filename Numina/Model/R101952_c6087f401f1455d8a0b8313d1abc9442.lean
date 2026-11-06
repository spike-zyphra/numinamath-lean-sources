import Mathlib

theorem number_theory_319594 (x y : ℕ) (hx : x > 0) (hy : y > 0)
    (hxy : x^2 + y^2 = 2000) :
    x + y = 52 ∨ x + y = 60 := by 
  have h1 : x ≤ 44 := by nlinarith
  have h2 : y ≤ 44 := by nlinarith
  interval_cases x <;> 
    interval_cases y 
    <;> norm_num at hxy 
    <;> norm_num 
    <;> tauto