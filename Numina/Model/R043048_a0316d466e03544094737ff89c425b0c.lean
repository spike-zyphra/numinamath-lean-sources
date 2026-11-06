import Mathlib

theorem number_theory_78876 : ¬∃ x y : ℤ, 59121 = x^2 + y^5 := by 
  rintro ⟨x, y, h⟩
  have h1 : x^2 % 11 = 0 ∨ x^2 % 11 = 1 ∨ x^2 % 11 = 3 ∨ x^2 % 11 = 4 ∨ x^2 % 11 = 5 ∨ x^2 % 11 = 9 := by 
    have h1 : x % 11 = 0 ∨ x % 11 = 1 ∨ x % 11 = 2 ∨ x % 11 = 3 ∨ x % 11 = 4 ∨ x % 11 = 5 ∨ x % 11 = 6 ∨ x % 11 = 7 ∨ x % 11 = 8 ∨ x % 11 = 9 ∨ x % 11 = 10 := by 
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1)
    · -- x ≡ 0
      simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- x ≡ 1
      simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- x ≡ 2
      simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- x ≡ 3
      simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- x ≡ 4
      simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- x ≡ 5
      simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- x ≡ 6
      simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- x ≡ 7
      simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- x ≡ 8
      simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- x ≡ 9
      simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- x ≡ 10
      simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
  
  have h3 : (x ^ 2 + y ^ 5) % 11 = 7 := by 
    omega
  
  have h4 : y ^ 5 % 11 = 0 ∨ y ^ 5 % 11 = 1 ∨ y ^ 5 % 11 = 10 := by 
    have h1 : y % 11 = 0 ∨ y % 11 = 1 ∨ y % 11 = 2 ∨ y % 11 = 3 ∨ y % 11 = 4 ∨ y % 11 = 5 ∨ y % 11 = 6 ∨ y % 11 = 7 ∨ y % 11 = 8 ∨ y % 11 = 9 ∨ y % 11 = 10 := by 
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1)
    · -- y ≡ 0
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> try { omega }
    · -- y ≡ 1
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> try { omega }
    · -- y ≡ 2
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- y ≡ 3
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- y ≡ 4
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- y ≡ 5
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- y ≡ 6
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- y ≡ 7
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- y ≡ 8
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- y ≡ 9
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- y ≡ 10
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
  
  omega