import Mathlib

open Real

theorem calculus_22955 : arctan (Real.sqrt 3) = Real.pi / 3 := by 
  have h1 : Real.sqrt 3 = Real.tan (Real.pi / 3) := by
    rw [Real.tan_pi_div_three]
  rw [h1]
  rw [Real.arctan_tan]
  all_goals linarith [Real.pi_pos]