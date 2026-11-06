import Mathlib

theorem number_theory_298041 (a b c : ℤ) (h : a > 0) (h' : b > 0) (h'' : c > 0)
    (h''' : a^2 + b^2 = c^2) :
    30 ∣ a * b * c := by

  have h2 : a % 2 = 0 ∨ b % 2 = 0 ∨ c % 2 = 0 := by
    by_contra h
    push_neg at h
    have ha1 : a % 2 = 1 := by omega
    have hb1 : b % 2 = 1 := by omega
    have hc1 : c % 2 = 1 := by omega
    have ha2 : a % 4 = 1 ∨ a % 4 = 3 := by 
      omega
    have hb2 : b % 4 = 1 ∨ b % 4 = 3 := by 
      omega
    have hc2 : c % 4 = 1 ∨ c % 4 = 3 := by
      omega
    have ha3 : a ^ 2 % 4 = 1 := by
      rcases ha2 with (h | h)
      · 
        simp [Int.add_emod, Int.mul_emod, pow_two, h, Int.ofNat]
      · 
        simp [Int.add_emod, Int.mul_emod, pow_two, h, Int.ofNat]
    have hb3 : b ^ 2 % 4 = 1 := by
      rcases hb2 with (h | h)
      · 
        simp [Int.add_emod, Int.mul_emod, pow_two, h, Int.ofNat]
      · 
        simp [Int.add_emod, Int.mul_emod, pow_two, h, Int.ofNat]
    have hc3 : c ^ 2 % 4 = 1 := by
      rcases hc2 with (h | h)
      · 
        simp [Int.add_emod, Int.mul_emod, pow_two, h, Int.ofNat]
      · 
        simp [Int.add_emod, Int.mul_emod, pow_two, h, Int.ofNat]
    have h4 : (a ^ 2 + b ^ 2) % 4 = c ^ 2 % 4 := by 
      omega
    omega

  have h3 : a % 3 = 0 ∨ b % 3 = 0 ∨ c % 3 = 0 := by
    by_contra h
    push_neg at h
    have ha1 : a % 3 = 1 ∨ a % 3 = 2 := by omega
    have hb1 : b % 3 = 1 ∨ b % 3 = 2 := by omega
    have hc1 : c % 3 = 1 ∨ c % 3 = 2 := by omega
    have h1 : (a ^ 2 + b ^ 2) % 3 = c ^ 2  % 3 := by omega
    have ha2 : a ^ 2 % 3 = 1 := by 
      rcases ha1 with (h | h)
      · 
        simp [Int.add_emod, Int.mul_emod, pow_two, h, Int.ofNat]
      · 
        simp [Int.add_emod, Int.mul_emod, pow_two, h, Int.ofNat]
    have hb2 : b ^ 2 % 3 = 1 := by 
      rcases hb1 with (h | h)
      · 
        simp [Int.add_emod, Int.mul_emod, pow_two, h, Int.ofNat]
      · 
        simp [Int.add_emod, Int.mul_emod, pow_two, h, Int.ofNat]
    have hc2 : c ^ 2 % 3 = 1 := by 
      rcases hc1 with (h | h)
      · 
        simp [Int.add_emod, Int.mul_emod, pow_two, h, Int.ofNat]
      · 
        simp [Int.add_emod, Int.mul_emod, pow_two, h, Int.ofNat]
    omega

  have h5 : a % 5 = 0 ∨ b % 5 = 0 ∨ c % 5 = 0 := by 
    by_contra h
    push_neg at h
    have ha1 : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
    have hb1 : b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by omega
    have hc1 : c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := by omega
    have h1 : (a ^ 2 + b ^ 2) % 5 = c ^ 2  % 5 := by omega
    have ha2 : a ^ 2 % 5 = 1 ∨ a ^ 2 % 5 = 4 := by
      rcases ha1 with (h | h | h | h) <;> 
        norm_num [Int.add_emod, Int.mul_emod, pow_two, h, Int.ofNat]
    have hb2 : b ^ 2 % 5 = 1 ∨ b ^ 2 % 5 = 4 := by
      rcases hb1 with (h | h | h | h) <;> 
        norm_num [Int.add_emod, Int.mul_emod, pow_two, h, Int.ofNat]
    have hc2 : c ^ 2 % 5 = 1 ∨ c ^ 2 % 5 = 4 := by
      rcases hc1 with (h | h | h | h) <;> 
        norm_num [Int.add_emod, Int.mul_emod, pow_two, h, Int.ofNat]
    omega

  -- Prove that 2 divides the product
  have h6 : (a * b * c) % 2 = 0 := by
    have : a % 2 = 0 ∨ b % 2 = 0 ∨ c % 2 = 0 := h2
    rcases this with (h | h | h)
    · simp [Int.mul_emod, h, Int.add_emod]
    · simp [Int.mul_emod, h, Int.add_emod]
    · simp [Int.mul_emod, h, Int.add_emod]

  -- Prove that 3 divides the product
  have h7 : (a * b * c) % 3 = 0 := by
    have : a % 3 = 0 ∨ b % 3 = 0 ∨ c % 3 = 0 := h3
    rcases this with (h | h | h)
    · simp [Int.mul_emod, h, Int.add_emod]
    · simp [Int.mul_emod, h, Int.add_emod]
    · simp [Int.mul_emod, h, Int.add_emod]

  -- Prove that 5 divides the product
  have h8 : (a * b * c) % 5 = 0 := by
    have : a % 5 = 0 ∨ b % 5 = 0 ∨ c % 5 = 0 := h5
    rcases this with (h | h | h)
    · simp [Int.mul_emod, h, Int.add_emod]
    · simp [Int.mul_emod, h, Int.add_emod]
    · simp [Int.mul_emod, h, Int.add_emod]

  omega