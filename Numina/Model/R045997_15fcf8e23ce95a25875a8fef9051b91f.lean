import Mathlib

theorem number_theory_301214 (x y z : ℤ) (h : x^2 + y^2 = z^2) :
    6 ∣ x * y := by
  have h4 : x * y % 2 = 0 := by
    by_contra h4
    push_neg at h4
    have h5 : x % 2 = 1 ∧ y % 2 = 1 := by
      have h6 : x % 2 = 1 := by
        by_contra h7
        push_neg at h7
        have h7' : x % 2 = 0 := by omega
        have h8 : (x * y) % 2 = 0 := by
          simp [Int.mul_emod, h7']
        omega
      have h7' : y % 2 = 1 := by 
        by_contra h7
        push_neg at h7
        have h7' : y % 2 = 0 := by omega
        have h8 : (x * y) % 2 = 0 := by
          simp [Int.mul_emod, h7']
        omega
      exact ⟨h6, h7'⟩
    have h6 : x % 2 = 1 := h5.1
    have h7 : y % 2 = 1 := h5.2
    have h8 : (x ^ 2 : ℤ) % 4 = 1 := by
      have h6' : x % 4 = 1 ∨ x % 4 = 3 := by 
        omega
      rcases h6' with (h6' | h6') <;> simp [pow_two, Int.add_emod, Int.mul_emod, h6']
    have h9 : (y ^ 2 : ℤ) % 4 = 1 := by
      have h6' : y % 4 = 1 ∨ y % 4 = 3 := by
        omega
      rcases h6' with (h6' | h6') <;> simp [pow_two, Int.add_emod, Int.mul_emod, h6']
    have h10 : (z ^ 2 : ℤ) % 4 = 0 ∨ (z ^ 2 : ℤ) % 4 = 1 := by
      have h6' : z % 4 = 0 ∨ z % 4 = 1 ∨ z % 4 = 2 ∨ z % 4 = 3 := by
        omega
      rcases h6' with (h6' | h6' | h6' | h6') <;> simp [pow_two, Int.add_emod, Int.mul_emod, h6']
    have h11 : (x^2 + y^2) % 4 = 2 := by
      omega
    have h12 : (z ^ 2) % 4 = 2 := by
      omega
    omega
  -- Show $3 \mid x * y$.
  have h5 : x * y % 3 = 0 := by
    by_contra h5
    push_neg at h5
    have h6 : x % 3 = 1 ∨ x % 3 = 2 := by
      by_contra h6
      push_neg at h6
      have : x % 3 = 0 := by
        omega
      have h7 : (x * y) % 3 = 0 := by 
        simp [Int.mul_emod, this]
      omega
    have h7 : y % 3 = 1 ∨ y % 3 = 2 := by 
      by_contra h7
      push_neg at h7
      have : y % 3 = 0 := by
        omega
      have h8 : (x * y) % 3 = 0 := by 
        simp [Int.mul_emod, this]
      omega
    have h8 : (x ^ 2 : ℤ) % 3 = 1 := by
      rcases h6 with (h6 | h6) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h6]
    have h9 : (y ^ 2 : ℤ) % 3 = 1 := by
      rcases h7 with (h7 | h7) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h7]
    have h10 : (z ^ 2 : ℤ) % 3 = 2 := by
      omega
    have h11 : (z ^ 2 : ℤ) % 3 = 0 ∨ (z ^ 2 : ℤ) % 3 = 1 := by
      have h6' : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by
        omega
      rcases h6' with (h6' | h6' | h6') <;> simp [pow_two, Int.add_emod, Int.mul_emod, h6']
    omega
  have h2 : 2 ∣ x * y := by 
    omega
  have h3 : 3 ∣ x * y := by
    omega
  omega