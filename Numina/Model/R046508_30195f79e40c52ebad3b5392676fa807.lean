import Mathlib

theorem number_theory_186160 (a b c : ℤ) (h : 7 ∣ a^3 + b^3 + c^3) :
    7 ∣ a ^ 3 ∨ 7 ∣ b ^ 3 ∨ 7 ∣ c ^ 3 := by
  by_contra h
  push_neg at h
  have h8 : a % 7 ≠ 0 := by 
    by_contra h9 
    have h9' : 7 ∣ a := by 
      omega 
    have h10 : 7 ∣ a ^ 3 := by 
      have h11 : 7 ∣ a := h9'
      have : a ^ 3 % 7 = 0 := by 
        have h11' : a % 7 = 0 := by omega 
        simp [h11', pow_succ, Int.add_emod, Int.mul_emod]
      omega 
    -- Now we reach a contradiction with h. 
    have h11 : 7 ∣ a ^ 3 ∨ 7 ∣ b ^ 3 ∨ 7 ∣ c ^ 3 := by 
      tauto 
    tauto 
  have h9 : b % 7 ≠ 0 := by 
    by_contra h10 
    have h11' : 7 ∣ b := by 
      omega 
    have h12 : 7 ∣ b ^ 3 := by 
      have h13 : 7 ∣ b := h11'
      have : b ^ 3 % 7 = 0 := by 
        have h13' : b % 7 = 0 := by omega 
        simp [h13', pow_succ, Int.add_emod, Int.mul_emod]
      omega 
    -- Now we reach a contradiction with h. 
    have h14 : 7 ∣ a ^ 3 ∨ 7 ∣ b ^ 3 ∨ 7 ∣ c ^ 3 := by 
      tauto 
    tauto 
  have h10 : c % 7 ≠ 0 := by 
    by_contra h11 
    have h12' : 7 ∣ c := by 
      omega 
    have h13 : 7 ∣ c ^ 3 := by 
      have h14 : 7 ∣ c := h12'
      have : c ^ 3 % 7 = 0 := by 
        have h14' : c % 7 = 0 := by omega 
        simp [h14', pow_succ, Int.add_emod, Int.mul_emod]
      omega 
    -- Now we reach a contradiction with h. 
    have h14 : 7 ∣ a ^ 3 ∨ 7 ∣ b ^ 3 ∨ 7 ∣ c ^ 3 := by 
      tauto 
    tauto 
  -- Now we need to derive a contradiction from the fact that none of a^3, b^3, c^3 is divisible by7. 
  -- Therefore, a^3, b^3, c^3 % 7 ∈ {1, 6}. Then the sum is not divisible by7. 
  have h4 : (a ^ 3 + b ^ 3 + c^3) % 7 = 0 := by 
    omega 
  -- Now we need to derive a contradiction from h4 and the fact that none of a^3, b^3, c^3 is divisible by7. 
  have h5 : a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by 
    omega 
  have h6 : b % 7 = 1 ∨ b % 7 = 2 ∨ b % 7 = 3 ∨ b % 7 = 4 ∨ b % 7 = 5 ∨ b % 7 = 6 := by 
    omega 
  have h7 : c % 7 = 1 ∨ c % 7 = 2 ∨ c % 7 = 3 ∨ c % 7 = 4 ∨ c % 7 = 5 ∨ c % 7 = 6 := by 
    omega 
  have h55 : a ^ 3 % 7 = 1 ∨ a ^ 3 % 7 = 6 := by 
    have h55 : a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := h5 
    rcases h55 with (h55 | h55 | h55 | h55 | h55 | h55) <;> simp [h55, pow_succ, Int.add_emod, Int.mul_emod]
  have h66 : b ^ 3 % 7 = 1 ∨ b ^ 3 % 7 = 6 := by 
    have h66 : b % 7 = 1 ∨ b % 7 = 2 ∨ b % 7 = 3 ∨ b % 7 = 4 ∨ b % 7 = 5 ∨ b % 7 = 6 := h6 
    rcases h66 with (h66 | h66 | h66 | h66 | h66 | h66) <;> simp [h66, pow_succ, Int.add_emod, Int.mul_emod]
  have h77 : c ^ 3 % 7 = 1 ∨ c ^ 3 % 7 = 6 := by 
    have h77 : c % 7 = 1 ∨ c % 7 = 2 ∨ c % 7 = 3 ∨ c % 7 = 4 ∨ c % 7 = 5 ∨ c % 7 = 6 := h7 
    rcases h77 with (h77 | h77 | h77 | h77 | h77 | h77) <;> simp [h77, pow_succ, Int.add_emod, Int.mul_emod]
  omega