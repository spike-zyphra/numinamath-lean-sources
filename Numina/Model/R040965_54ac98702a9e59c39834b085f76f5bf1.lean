import Mathlib
set_option maxRecDepth 10000

theorem Number_Theory_609424 :
  ∃ E : ℤ, E = (-1) ^ (101 * 10) * ((-2)^10 - 1) ∧ E % 101 = 13 := by
  use (-1) ^ (101 * 10) * ((-2)^10 - 1)
  constructor
  · -- Show the equality holds trivially since the definition matches the claimed value
    rfl 
  · -- Now compute the modulus
    norm_num