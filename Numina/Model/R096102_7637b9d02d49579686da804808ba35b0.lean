import Mathlib

theorem algebra_21703 : (-(2 / 5) * Complex.I)^2 = -4 / 25 := by 
  simp [pow_two, Complex.ext_iff, Complex.I_sq]
  all_goals norm_num