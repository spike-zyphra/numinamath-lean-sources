import Mathlib

theorem number_theory_254027 {A B C : ℤ} (h : A^2 + B^2 = C^2) :
    6 ∣ A * B := by 
  have h1 : A % 2 = 0 ∨ A % 2 = 1 := by 
    omega
  have h2 : B % 2 = 0 ∨ B % 2 = 1 := by 
    omega
  have h3 : (A % 4 = 0 ∨ A % 4 = 1 ∨ A % 4 = 2 ∨ A % 4 = 3) := by 
    omega
  have h4 : (B % 4 = 0 ∨ B % 4 = 1 ∨ B % 4 = 2 ∨ B % 4 = 3) := by 
    omega
  have h5 : (C % 4 = 0 ∨ C % 4 = 1 ∨ C % 4 = 2 ∨ C % 4 = 3) := by 
    omega
  have h6 : A^2 % 4 = 0 ∨ A^2 % 4 = 1 := by
    rcases h3 with (h | h | h | h) <;> 
      simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.emod]
  have h7 : B^2 % 4 = 0 ∨ B^2 % 4 = 1 := by
    rcases h4 with (h | h | h | h) <;> 
      simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.emod]
  have h8 : C^2 % 4 = 0 ∨ C^2 % 4 = 1 := by 
    rcases h5 with (h | h | h | h) <;> 
      simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.emod]
  have h9 : (A ^ 2 + B ^ 2) % 4 = C^2 % 4 := by 
    omega
  have h10 : A % 2 = 0 ∨ B % 2 = 0 := by 
    by_contra h
    push_neg at h
    have ha1 : A % 2 = 1 := by 
      omega
    have hb1 : B % 2 = 1 := by 
      omega
    have h11 : A % 4 = 1 ∨ A % 4 = 3 := by 
      have h12 : A % 2 = 1 := by 
        omega
      omega
    have h12 : B % 4 = 1 ∨ B % 4 = 3 := by 
      have h13 : B % 2 = 1 := by 
        omega
      omega
    have h13 : A ^ 2 % 4 = 1 := by 
      rcases h11 with (h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.emod]
    have h14 : B ^ 2 % 4 = 1 := by 
      rcases h12 with (h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.emod]
    have h15 : (A ^ 2 + B ^ 2) % 4 = 2 := by 
      omega
    omega
  have h11 : (A * B) % 2 = 0 := by 
    rcases h10 with (h | h)
    · -- A is even 
      have ha1 : A % 2 = 0 := by 
        omega
      simp [Int.mul_emod, ha1, Int.emod]
    · -- B is even 
      have hb1 : B % 2 = 0 := by 
        omega
      simp [Int.mul_emod, hb1, Int.emod]
  have h12 : (A * B) % 3 = 0 := by
    have h13 : A % 3 = 0 ∨ A % 3 = 1 ∨ A % 3 = 2 := by
      omega
    have h14 : B % 3 = 0 ∨ B % 3 = 1 ∨ B % 3 = 2 := by
      omega
    have h15 : C % 3 = 0 ∨ C % 3 = 1 ∨ C % 3 = 2 := by
      omega 
    have h16 : A ^ 2 % 3 = 0 ∨ A ^ 2 % 3 = 1 := by 
      rcases h13 with (h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.emod]
    have h17 : B ^ 2 % 3 = 0 ∨ B ^ 2 % 3 = 1 := by 
      rcases h14 with (h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.emod]
    have h18 : C ^ 2 % 3 = 0 ∨ C ^ 2 % 3 = 1 := by 
      rcases h15 with (h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.emod]
    have h19 : (A ^ 2 + B ^ 2) % 3 = C^2 % 3 := by
      omega 
    -- Show that if neither A nor B is 0 mod 3, then we have a contradiction
    have h20 : A % 3 = 0 ∨ B % 3 = 0 := by
      by_contra h
      push_neg at h
      have h21 : A % 3 = 1 ∨ A % 3 = 2 := by
        omega
      have h22 : B % 3 = 1 ∨ B % 3 = 2 := by 
        omega
      have h23 : A ^ 2 % 3 = 1 := by
        rcases h21 with (h | h) <;> 
          simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.emod]
      have h24 : B ^ 2 % 3 = 1 := by
        rcases h22 with (h | h) <;> 
          simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.emod]
      have h25 : (A ^ 2 + B ^ 2) % 3 = 2 := by 
        omega 
      omega 
    rcases h20 with (h | h)
    · -- A % 3 = 0 
      simp [Int.mul_emod, h, Int.emod]
    · -- B % 3 = 0
      simp [Int.mul_emod, h, Int.emod]
  omega