import Mathlib

theorem number_theory_144543 (x y z : ℤ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : x^2 + y^2 = z^2) :
    (3 ∣ x ∨ 3 ∣ y) ∧ (5 ∣ x ∨ 5 ∣ y ∨ 5 ∣ z) := by

  have h1 : 3 ∣ x ∨ 3 ∣ y := by 
    by_contra h2
    push_neg at h2

    have h1 : x % 3 = 1 ∨ x % 3 = 2 := by 
      omega

    have h2 : y % 3 = 1 ∨ y % 3 = 2 := by 
      omega

    have h3 : x^2 % 3 = 1 := by 
      rcases h1 with (h1 | h1)
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h1]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h1]
    
    have h4 : y^2 % 3 = 1 := by 
      rcases h2 with (h2 | h2)
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h2]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h2]

    have h5 : (x^2 + y^2) % 3 = 2 := by 
      omega

    have h6 : z^2 % 3 = 2 := by 
      omega

    have h7 : z^2 % 3 = 0 ∨ z^2 % 3 = 1 := by 
      have h8 : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by 
        omega
      rcases h8 with (h8 | h8 | h8)
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h8]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h8]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h8]

    omega

  have h2 : 5 ∣ x ∨ 5 ∣ y ∨ 5 ∣ z := by 
    by_contra h3
    push_neg at h3

    have h4 : x % 5 ≠ 0 := by 
      omega
    have h5 : y % 5 ≠ 0 := by 
      omega
    have h6 : z % 5 ≠ 0 := by 
      omega

    have h7 : x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by 
      omega

    have h8 : y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by 
      omega

    have h9 : z % 5 = 1 ∨ z % 5 = 2 ∨ z % 5 = 3 ∨ z % 5 = 4 := by 
      omega

    have h10 : x^2 % 5 = 1 ∨ x^2 % 5 = 4 := by 
      rcases h7 with (h | h | h | h)
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h]

    have h11 : y^2 % 5 = 1 ∨ y^2 % 5 = 4 := by 
      rcases h8 with (h | h | h | h)
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h]

    have h12 : z^2 % 5 = 1 ∨ z^2 % 5 = 4 := by 
      rcases h9 with (h | h | h | h)
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h]

    have h13 : (x^2 + y^2) % 5 = z^2 % 5 := by 
      omega

    omega

  exact ⟨h1, h2⟩