import Mathlib

theorem number_theory_122762 (x y z : ℤ) (h : x^2 + y^2 = z^2) :
    2 ∣ x ∨ 2 ∣ y := by
  by_contra h1
  push_neg at h1
  have hx1 : x % 2 = 1 := by
    by_contra h
    push_neg at h
    have : x % 2 = 0 := by
      omega
    have h2 : 2 ∣ x := by
      omega
    tauto
  have hy1 : y % 2 = 1 := by
    by_contra h
    push_neg at h
    have : y % 2 = 0 := by
      omega
    have h2 : 2 ∣ y := by
      omega
    tauto
  have h2 : x % 4 = 1 ∨ x % 4 = 3 := by 
    omega
  have h3 : y % 4 = 1 ∨ y % 4 = 3 := by 
    omega
  have h4 : x^2 % 4 = 1 := by
    rcases h2 with (h2 | h2)
    · -- x ≡ 1 [MOD 4]
      norm_num [pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod, h2]
    · -- x ≡ 3 [MOD 4]
      norm_num [pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod, h2]
  have h5 : y^2 % 4 = 1 := by
    rcases h3 with (h3 | h3)
    · -- y ≡ 1 [MOD 4]
      norm_num [pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod, h3]
    · -- y ≡ 3 [MOD 4]
      norm_num [pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod, h3]
  have h6 : (x^2 + y^2) % 4 = 2 := by
    omega
  have h7 : z^2 % 4 = 0 ∨ z^2 % 4 = 1 := by
    have h1 : z % 4 = 0 ∨ z % 4 = 1 ∨ z % 4 = 2 ∨ z % 4 = 3 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1) <;> norm_num [pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod, h1]
  have h8 : z^2 % 4 = 2 := by 
    omega
  omega