import Mathlib

theorem algebra_1158 : abs (Real.pi - abs (Real.pi - 7)) = 7 - 2 * Real.pi := by
  have h1 : abs (Real.pi - 7) = 7 - Real.pi := by 
    have h2 : Real.pi < 7 := by 
      linarith [Real.pi_lt_315]
    rw [abs_of_neg (by linarith)]
    linarith
  have h3 : abs (Real.pi - abs (Real.pi - 7)) = abs (Real.pi - (7 - Real.pi)) := by 
    rw [h1]
    all_goals norm_num
  rw [h3]
  have h4 : 2 * Real.pi < 7 := by 
    nlinarith [Real.pi_lt_315]
  have h5 : Real.pi - (7 - Real.pi) < 0 := by 
    linarith [h4]
  rw [abs_of_neg h5]
  linarith