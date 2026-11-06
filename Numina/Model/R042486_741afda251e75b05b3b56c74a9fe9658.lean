import Mathlib

theorem algebra_225779 (n : ℤ) :
    6 ∣ n * (2 + 3 * n + n ^ 2) := by 
  have h1 : n * (2 + 3 * n + n ^ 2) % 2 = 0 := by 
    have h2 : n % 2 = 0 ∨ n % 2 = 1 := by 
      omega 
    rcases h2 with (h2 | h2)
    · 
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h2] 
    · 
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h2] 
  have h3 : n * (2 + 3 * n + n ^ 2) % 3 = 0 := by 
    have h4 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by 
      omega 
    rcases h4 with (h4 | h4 | h4)
    · 
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h4] 
    · 
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h4] 
    · 
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h4] 
  omega