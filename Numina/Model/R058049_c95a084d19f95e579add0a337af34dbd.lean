import Mathlib

theorem algebra_2103 {a : ℚ} (ha : a ≠ -2000) :
    11 / (a + 2000) ≠ 0 := by 
  have h1 : a + 2000 ≠ 0 := by
    intro h
    have : a = -2000 := by linarith 
    contradiction 
  apply (div_ne_zero_iff).mpr 
  constructor 
  · norm_num 
  · exact h1