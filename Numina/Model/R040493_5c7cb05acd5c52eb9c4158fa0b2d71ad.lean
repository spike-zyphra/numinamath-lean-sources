import Mathlib

theorem number_theory_107207 (a : ℤ) : 10 ∣ a^73 - a^37 := by
  have h1 : a ^ 73 % 2 = a ^ 37 % 2 := by
    have h1 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rcases h1 with (h1 | h1)
    ·
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    ·
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
  
  have h2 : a ^ 73 % 5 = a ^ 37 % 5 := by 
    have h1 : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1)
    · 
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · 
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · 
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · 
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · 
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]

  omega