import Mathlib

theorem algebra_12846 (people days : ℝ) (hpeople : people = 2000) (hdays : days = 3) :
    round (people / (days * 24)) = 28 := by 
  rw [hpeople, hdays]
  norm_num [round_eq]