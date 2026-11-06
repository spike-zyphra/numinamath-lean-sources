import Mathlib

theorem number_theory_271284 (n : ℤ) : 30 ∣ n^5 - n := by
  have h1 : n^5 % 2 = n % 2 := by 
    have h : n % 2 = 0 ∨ n % 2 = 1 := by 
      omega
    rcases h with (h | h)
    · 
      simp [pow_succ, Int.mul_emod, h]
    · 
      simp [pow_succ, Int.mul_emod, h]
  
  have h2 : n^5 % 3 = n % 3 := by 
    have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by 
      omega
    rcases h with (h | h | h)
    · 
      simp [pow_succ, Int.mul_emod, h]
    · 
      simp [pow_succ, Int.mul_emod, h]
    · 
      simp [pow_succ, Int.mul_emod, h]

  have h3 : n^5 % 5 = n % 5 := by 
    have h : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by 
      omega
    rcases h with (h | h | h | h | h)
    · 
      simp [pow_succ, Int.mul_emod, h]
    · 
      simp [pow_succ, Int.mul_emod, h]
    · 
      simp [pow_succ, Int.mul_emod, h]
    · 
      simp [pow_succ, Int.mul_emod, h]
    · 
      simp [pow_succ, Int.mul_emod, h]

  omega