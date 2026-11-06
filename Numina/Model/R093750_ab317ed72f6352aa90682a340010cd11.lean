import Mathlib

theorem number_theory_6059 (x y z : ℤ) (h : x^2 + y^2 + z^2 = 100) :
    (3 ∣ x ∨ 3 ∣ y) ∧ (5 ∣ x ∨ 5 ∣ y ∨ 5 ∣ z) := by 
  have h1 : 3 ∣ x ∨ 3 ∣ y := by 
    by_contra h1
    push_neg at h1
    have h2 : x % 3 = 1 ∨ x % 3 = 2 := by
      omega
    have h3 : y % 3 = 1 ∨ y % 3 = 2 := by
      omega
    have h4 : x^2 % 3 = 1 := by 
      rcases h2 with (h2 | h2)
      ·
        simp [pow_two, Int.add_emod, Int.mul_emod, h2]
      ·
        simp [pow_two, Int.add_emod, Int.mul_emod, h2]
    have h5 : y^2 % 3 = 1 := by 
      rcases h3 with (h3 | h3)
      ·
        simp [pow_two, Int.add_emod, Int.mul_emod, h3]
      ·
        simp [pow_two, Int.add_emod, Int.mul_emod, h3]
    have h6 : (x^2 + y^2 + z^2) % 3 = 1 % 3 := by 
      omega
    have h7 : (x^2 + y^2 + z^2) % 3 = (1 + 1 + z^2 % 3) % 3 := by 
      omega
    have h8 : z^2 % 3 = 0 ∨ z^2 % 3 = 1 := by 
      have h9 : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by 
        omega
      rcases h9 with (h9 | h9 | h9)
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h9]
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h9]
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h9]
    omega 
  have h2 : 5 ∣ x ∨ 5 ∣ y ∨ 5 ∣ z := by 
    by_contra h2
    push_neg at h2
    have h3 : x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by 
      omega 
    have h4 : y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by 
      omega 
    have h5 : z % 5 = 1 ∨ z % 5 = 2 ∨ z % 5 = 3 ∨ z % 5 = 4 := by 
      omega 
    have h6 : x^2 % 5 = 1 ∨ x^2 % 5 = 4 := by 
      rcases h3 with (h3 | h3 | h3 | h3)
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h3]
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h3]
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h3]
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h3]
    have h7 : y^2 % 5 = 1 ∨ y^2 % 5 = 4 := by 
      rcases h4 with (h4 | h4 | h4 | h4)
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h4]
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h4]
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h4]
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h4]
    have h8 : z^2 % 5 = 1 ∨ z^2 % 5 = 4 := by 
      rcases h5 with (h5 | h5 | h5 | h5)
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h5]
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h5]
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h5]
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h5]
    have h9 : (x^2 + y^2 + z^2) % 5 = 0 := by 
      omega
    have h10 : (x^2 + y^2 + z^2) % 5 = (x^2 % 5 + y^2 % 5 + z^2 % 5) % 5 := by 
      omega 
    omega 
  constructor 
  · exact h1 
  · exact h2