import Mathlib

theorem number_theory_7797 (x y z : ℤ) (h : x^2 + y^2 = z^2) :
    (3 ∣ x ∨ 3 ∣ y ∨ 3 ∣ z) ∧ (4 ∣ x ∨ 4 ∣ y ∨ 4 ∣ z) ∧
    (5 ∣ x ∨ 5 ∣ y ∨ 5 ∣ z) := by 
  constructor
  · -- Show either 3 divides x, 3 divides y, or 3 divides z
    by_contra h1
    push_neg at h1
    have h2 : x % 3 = 1 ∨ x % 3 = 2 := by
      omega
    have h3 : y % 3 = 1 ∨ y % 3 = 2 := by
      omega
    have h4 : z % 3 = 1 ∨ z % 3 = 2 := by
      omega
    have h5 : x ^ 2 % 3 = 1 := by
      rcases h2 with (h2 | h2) <;> simp [pow_two, Int.mul_emod, Int.add_emod, h2, Int.ofNat]
    have h6 : y ^ 2 % 3 = 1 := by
      rcases h3 with (h3 | h3) <;> simp [pow_two, Int.mul_emod, Int.add_emod, h3, Int.ofNat]
    have h7 : z ^ 2 % 3 = 1 := by
      rcases h4 with (h4 | h4) <;> simp [pow_two, Int.mul_emod, Int.add_emod, h4, Int.ofNat]
    have h8 : (x ^ 2 + y ^ 2) % 3 = z ^ 2 % 3 := by 
      omega
    omega
  constructor
  · -- Show either 4 divides x, 4 divides y, or 4 divides z
    by_contra h1
    push_neg at h1
    have h2 : x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by 
      omega
    have h3 : y % 8 = 1 ∨ y % 8 = 2 ∨ y % 8 = 3 ∨ y % 8 = 5 ∨ y % 8 = 6 ∨ y % 8 = 7 := by 
      omega
    have h4 : z % 8 = 1 ∨ z % 8 = 2 ∨ z % 8 = 3 ∨ z % 8 = 5 ∨ z % 8 = 6 ∨ z % 8 = 7 := by 
      omega
    have h5 : x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2) <;> norm_num [h2, pow_two, Int.add_emod, Int.mul_emod]
    have h6 : y ^ 2 % 8 = 1 ∨ y ^ 2 % 8 = 4 := by
      rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3) <;> norm_num [h3, pow_two, Int.add_emod, Int.mul_emod]
    have h7 : z ^ 2 % 8 = 1 ∨ z ^ 2 % 8 = 4 := by
      rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4) <;> norm_num [h4, pow_two, Int.add_emod, Int.mul_emod]
    have h8 : (x ^ 2 + y ^ 2) % 8 = z ^ 2 % 8 := by 
      omega
    omega
  · -- Show either 5 divides x, 5 divides y, or 5 divides z
    by_contra h1
    push_neg at h1
    have h2 : x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by 
      omega
    have h3 : y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by 
      omega
    have h4 : z % 5 = 1 ∨ z % 5 = 2 ∨ z % 5 = 3 ∨ z % 5 = 4 := by 
      omega
    have h5 : x^2 % 5 = 1 ∨ x^2 % 5 = 4 := by 
      rcases h2 with (h2 | h2 | h2 | h2) <;> 
        norm_num [h2, pow_two, Int.add_emod, Int.mul_emod]
    have h6 : y^2 % 5 = 1 ∨ y^2 % 5 = 4 := by 
      rcases h3 with (h3 | h3 | h3 | h3) <;> 
        norm_num [h3, pow_two, Int.add_emod, Int.mul_emod]
    have h7 : z^2  % 5 = 1 ∨ z^2 % 5 = 4 := by 
      rcases h4 with (h4 | h4 | h4 | h4) <;> 
        norm_num [h4, pow_two, Int.add_emod, Int.mul_emod]
    have h8 : (x ^ 2 + y ^ 2) % 5 = z ^ 2 % 5 := by 
      omega
    omega