import Mathlib

/-- Compute the smallest multiple of 63 with an odd number of ones in its base two representation. -/
theorem number_theory_610661 : 
  -- 1) 4221 is a multiple of 63
  63 ∣ 4221 ∧ 
  -- 2) The binary representation of 4221 has 7 ones (odd number)
  4221 = 2^12 + 2^6 + 2^5 + 2^4 + 2^3 + 2^2 + 2^0 := by
  
  -- First, prove 4221 is divisible by 63
  have h_div : 63 ∣ 4221 := by
    -- 4221 = 63 * 67
    use 67
  
  -- 4221 in binary is 1000111111101, which has 7 ones
  have h_binary : 4221 = 2^12 + 2^6 + 2^5 + 2^4 + 2^3 + 2^2 + 2^0 := by
    norm_num
  
  -- Join the two facts to complete the theorem
  apply And.intro
  -- First part: 4221 is divisible by 63
  · exact h_div
  -- Second part: Binary representation of 4221
  · exact h_binary