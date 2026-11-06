import Mathlib

theorem algebra_2104 (a : ℝ) (ha : a < 0) : Real.sqrt (-a^3) = -a * Real.sqrt (-a) := by
  have h1 : -a > 0 := by linarith
  have h2 : -a^3 = (-a) * (a^2) := by 
    ring
  rw [h2]
  have h3 : Real.sqrt ((-a) * (a^2)) = Real.sqrt (-a) * Real.sqrt (a^2) := by
    rw [Real.sqrt_mul (by positivity)]
  have h4 : Real.sqrt (a^2) = -a := by
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_neg ha]
  rw [h3, h4]
  all_goals linarith