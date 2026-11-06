import Mathlib

theorem number_theory_610661 : 
  -- 1) 4221 is a multiple of 63
  63 ∣ 4221 ∧ 
  -- 2) The binary representation of 4221 has 7 ones (odd number)
  4221 = 2^12 + 2^6 + 2^5 + 2^4 + 2^3 + 2^2 + 2^0 := by
  constructor
  · -- Verify that 4221 is a multiple of 63
    norm_num
  · -- Verify that 4221 equals the given binary representation
    norm_num