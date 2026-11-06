import Mathlib

theorem number_theory_236959 (a b c : ℤ) (h₀ : a^2 + b^2 = c^2) :
    5 ∣ a ∨ 5 ∣ b ∨ 5 ∣ c := by
  by_contra h
  push_neg at h
  have h1 : ¬ (5 ∣ a) := h.1
  have h2 : ¬ (5 ∣ b) := h.2.1
  have h3 : ¬ (5 ∣ c) := h.2.2
  
  -- Compute possible values of a^2 mod 5, b^2 mod 5 and c^2 mod 5
  have h4 : a^2 % 5 = 1 ∨ a^2 % 5 = 4 := by 
    have h5 : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by
      omega
    rcases h5 with (h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h] 

  have h6 : b^2 % 5 = 1 ∨ b^2 % 5 = 4 := by 
    have h7 : b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by 
      omega
    rcases h7 with (h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h] 

  have h8 : c^2 % 5 = 1 ∨ c^2 % 5 = 4 := by 
    have h9 : c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := by 
      omega
    rcases h9 with (h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h] 

  -- Compute all possible values of (a^2 + b^2) % 5
  have h10 : (a^2 + b^2) % 5 = 0 ∨ (a^2 + b^2) % 5 = 2 ∨ (a^2 + b^2) % 5 = 3 := by
    rcases h4 with (h4 | h4) <;> rcases h6 with (h6 | h6) <;> omega
  
  -- From h₀, we also have (a^2 + b^2) % 5 = c^2 % 5
  have h11 : (a^2 + b^2) % 5 = c^2 % 5 := by 
    omega
  
  -- Now we have (a^2 + b^2) % 5 must be 0, 2, or 3, but c^2 % 5 must be 1 or 4
  -- So this is a contradiction
  rcases h10 with (h10 | h10 | h10) <;> rcases h8 with (h8 | h8) <;> omega