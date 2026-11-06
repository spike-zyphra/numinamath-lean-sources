import Mathlib

theorem number_theory_278787 (a : ℤ) : 42 ∣ a^7 - a := by
  have h1 : a^7 % 2 = a % 2 := by
    have h1 : a % 2 = 0 ∨ a % 2 = 1 := by
      omega
    rcases h1 with (h | h)
    · 
      simp [pow_succ, Int.mul_emod, Int.add_emod, h]
    · 
      simp [pow_succ, Int.mul_emod, Int.add_emod, h]
  
  have h2 : a^7 % 3 = a % 3 := by 
    have h2 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by
      omega
    rcases h2 with (h | h | h)
    · 
      simp [pow_succ, Int.mul_emod, Int.add_emod, h]
    · 
      simp [pow_succ, Int.mul_emod, Int.add_emod, h]
    · 
      simp [pow_succ, Int.mul_emod, Int.add_emod, h]
  
  have h3 : a^7 % 7 = a % 7 := by
    have h3 : a % 7 = 0 ∨ a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by
      omega
    rcases h3 with (h | h | h | h | h | h | h)
    · 
      simp [pow_succ, Int.mul_emod, Int.add_emod, h]
    · 
      simp [pow_succ, Int.mul_emod, Int.add_emod, h]
    · 
      simp [pow_succ, Int.mul_emod, Int.add_emod, h]
    · 
      simp [pow_succ, Int.mul_emod, Int.add_emod, h]
    · 
      simp [pow_succ, Int.mul_emod, Int.add_emod, h]
    · 
      simp [pow_succ, Int.mul_emod, Int.add_emod, h]
    · 
      simp [pow_succ, Int.mul_emod, Int.add_emod, h]

  omega