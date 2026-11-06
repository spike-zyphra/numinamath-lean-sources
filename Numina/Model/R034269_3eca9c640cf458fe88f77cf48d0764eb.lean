import Mathlib

theorem number_theory_253788 (n : ℤ) (h : ∃ m, m^3 = n + 1) :
    504 ∣ n * (n + 1) * (n + 2) := by
  rcases h with ⟨m, hm⟩
  have h1 : n * (n + 1) * (n + 2) = (m ^ 3 - 1) * m ^ 3 * (m ^ 3 + 1) := by
    have h2 : n = m ^ 3 - 1 := by 
      nlinarith [hm]
    rw [h2]
    <;> ring
  rw [h1] 
  have h2 : (m ^ 3 - 1) * m ^ 3 * (m ^ 3 + 1) % 8 = 0 := by
    have h3 : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 4 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by 
      omega 
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> simp [h3, Int.add_emod, Int.mul_emod, pow_two, pow_three, Int.sub_emod]
    
  have h3 : (m ^ 3 - 1) * m ^ 3 * (m ^ 3 + 1) % 9 = 0 := by
    have h4 : m % 9 = 0 ∨ m % 9 = 1 ∨ m % 9 = 2 ∨ m % 9 = 3 ∨ m % 9 = 4 ∨ m % 9 = 5 ∨ m % 9 = 6 ∨ m % 9 = 7 ∨ m % 9 = 8 := by 
      omega 
    rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> simp [h4, Int.add_emod, Int.mul_emod, pow_two, pow_three, Int.sub_emod]
    
  have h4 : (m ^ 3 - 1) * m ^ 3 * (m ^ 3 + 1) % 7 = 0 := by
    have h5 : m % 7 = 0 ∨ m % 7 = 1 ∨ m % 7 = 2 ∨ m % 7 = 3 ∨ m % 7 = 4 ∨ m % 7 = 5 ∨ m % 7 = 6 := by 
      omega 
    rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5) <;> simp [h5, Int.add_emod, Int.mul_emod, pow_two, pow_three, Int.sub_emod]
    
  omega